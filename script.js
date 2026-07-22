/* ============================================================
   VOLTRA — application script begins.
   Sections:
     1. Utilities & constants
     2. Component library (definitions + symbolic/realistic draw)
     3. Circuit data model
     4. Netlist / node extraction
     5. MNA linear-algebra solver
     6. DC + transient simulation engine
     7. Rendering pipeline
     8. Interaction (mouse/keyboard/palette/drag)
     9. Right panel (properties / netlist / console)
    10. Oscilloscope + meters
    11. Save/Load + examples
    12. Boot
============================================================ */

/* ============================================================
   1. UTILITIES & CONSTANTS
============================================================ */
const GRID = 20;                 // px per grid unit at zoom 1
const TERM_R = 4;                // terminal dot radius (schematic)
const SNAP = 0.5;                // snap to half grid units (matches component terminal offsets)

const state = {
  view: 'schematic',             // 'schematic' | 'realistic'
  theme: 'dark',                 // 'dark' | 'light' — kept in sync with <html data-theme>
  tool: 'select',                // 'select' | 'wire' | 'probe' | 'delete'
  zoom: 1,
  pan: {x: 0, y: 0},
  dragging: null,                // active drag info
  wireDraft: null,                // {from:{x,y}, points:[...]}
  selection: new Set(),
  wireSelection: new Set(),
  hoverTerm: null,
  running: false,
  runTimer: null,
  t: 0,                          // simulation time (s)
  dt: 0.0002,                    // simulation timestep (s)
  simSpeed: 1,                   // simulation speed multiplier
  history: {t:[], series:{}},    // scope trace history
  probes: [],                    // active voltage probes [{a:{x,y}, b:{x,y}|null, id}]
  nextId: 1,
  clipboard: null,
};

/* ---- theme-aware palette used by canvas-drawn elements (grid,
   wires, component outlines) since <canvas> paints can't read
   CSS custom properties on their own. Kept in lockstep with the
   :root / [data-theme="light"] tokens in styles.css. ---- */
const THEME_COLORS = {
  dark:  { bg:'#12151b', gridDot:'rgba(154,164,184,0.14)', gridLine:'rgba(154,164,184,0.05)',
           compStroke:'#c7cbd6', wire:'#7f8ba0', junction:'#7f8ba0' },
  light: { bg:'#f4f5f8', gridDot:'rgba(60,68,88,0.16)', gridLine:'rgba(60,68,88,0.08)',
           compStroke:'#2c3342', wire:'#556074', junction:'#556074' },
};
function themeColors(){ return THEME_COLORS[state.theme] || THEME_COLORS.dark; }

function uid(prefix){ return prefix + (state.nextId++); }

function snap(v){ return Math.round(v / SNAP) * SNAP; }

function fmtEng(value, unit){
  if (value === undefined || value === null || Number.isNaN(value)) return '—';
  const a = Math.abs(value);
  const prefixes = [
    {v:1e9,  s:'G'}, {v:1e6, s:'M'}, {v:1e3, s:'k'},
    {v:1,    s:''},
    {v:1e-3, s:'m'}, {v:1e-6, s:'µ'}, {v:1e-9, s:'n'}, {v:1e-12,s:'p'}
  ];
  if (a === 0) return '0 ' + unit;
  for (const p of prefixes){
    if (a >= p.v){
      const n = value / p.v;
      const digits = a >= p.v*100 ? 0 : (a >= p.v*10 ? 1 : 2);
      return n.toFixed(digits) + ' ' + p.s + unit;
    }
  }
  return value.toExponential(2) + ' ' + unit;
}

function parseEng(str){
  if (typeof str === 'number') return str;
  if (!str) return NaN;
  str = String(str).trim();
  const m = str.match(/^(-?[\d.]+)\s*([a-zA-Zµ\u03bc]*)$/);
  if (!m) return parseFloat(str);
  const n = parseFloat(m[1]);
  const suf = m[2].toLowerCase();
  const map = {
    'g':1e9, 'meg':1e6, 'k':1e3, '':1, 'm':1e-3,
    'u':1e-6, 'µ':1e-6, 'μ':1e-6, 'n':1e-9, 'p':1e-12, 'f':1e-15
  };
  if (suf in map) return n * map[suf];
  if (suf === 'm' ) return n * 1e-3;
  return n;
}

/* ---- multi-waveform generator for AC-type sources -----------
   Supports sine, square, triangle and sawtooth, all phase-aligned
   so switching waveform type at the same phase setting doesn't
   jump the starting point around. `phaseDeg` shifts the waveform
   by that many degrees of one period. ---- */
function acWaveformValue(type, amplitude, freqHz, phaseDeg, t){
  const f = Math.max(1e-6, freqHz);
  let x = (f * t) + ((phaseDeg||0) / 360); // phase in cycles
  x = x - Math.floor(x); // wrap to [0,1)
  switch(type){
    case 'square':
      return x < 0.5 ? amplitude : -amplitude;
    case 'triangle':
      if (x < 0.25) return amplitude * (4*x);
      if (x < 0.75) return amplitude * (2 - 4*x);
      return amplitude * (4*x - 4);
    case 'sawtooth':
      return amplitude * (2*((x + 0.5) % 1) - 1);
    case 'sine':
    default:
      return amplitude * Math.sin(2*Math.PI*x);
  }
}

function log(msg, kind){
  const el = document.getElementById('console-out');
  const line = document.createElement('div');
  line.className = 'log-line' + (kind ? ' ' + kind : '');
  const t = new Date();
  const ts = t.toLocaleTimeString('en-US', {hour12:false}) + '.' + String(t.getMilliseconds()).padStart(3,'0');
  line.innerHTML = '<span class="log-time">' + ts + '</span>' + escapeHtml(msg);
  el.prepend(line);
  while (el.children.length > 200) el.removeChild(el.lastChild);
}

function escapeHtml(s){
  return String(s).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
}

function toast(msg, kind){
  const wrap = document.getElementById('toastwrap');
  const t = document.createElement('div');
  t.className = 'toast' + (kind ? ' ' + kind : '');
  t.textContent = msg;
  wrap.appendChild(t);
  setTimeout(() => { t.style.opacity = '0'; t.style.transition = 'opacity .25s'; setTimeout(()=>t.remove(), 260); }, 2600);
}

function dist(a, b){ return Math.hypot(a.x-b.x, a.y-b.y); }
function pointKey(p){ return Math.round(p.x*100)+','+Math.round(p.y*100); }

// small dense-matrix linear solver (Gaussian elimination, partial pivot)
function solveLinear(Aorig, borig){
  const n = borig.length;
  const A = Aorig.map(r => r.slice());
  const b = borig.slice();
  for (let col = 0; col < n; col++){
    let piv = col, best = Math.abs(A[col][col]);
    for (let r = col+1; r < n; r++){
      if (Math.abs(A[r][col]) > best){ best = Math.abs(A[r][col]); piv = r; }
    }
    if (best < 1e-14){ continue; } // singular-ish; leave as is (handled by regularization upstream)
    if (piv !== col){
      [A[col], A[piv]] = [A[piv], A[col]];
      [b[col], b[piv]] = [b[piv], b[col]];
    }
    const pv = A[col][col];
    for (let r = col+1; r < n; r++){
      const f = A[r][col] / pv;
      if (f === 0) continue;
      for (let c = col; c < n; c++) A[r][c] -= f * A[col][c];
      b[r] -= f * b[col];
    }
  }
  const x = new Array(n).fill(0);
  for (let r = n-1; r >= 0; r--){
    let s = b[r];
    for (let c = r+1; c < n; c++) s -= A[r][c]*x[c];
    x[r] = Math.abs(A[r][r]) < 1e-14 ? 0 : s / A[r][r];
  }
  return x;
}

// rotate a local {x,y} point by quarter turns (0..3) around origin
function rotPt(p, q){
  switch(((q%4)+4)%4){
    case 0: return {x:p.x, y:p.y};
    case 1: return {x:-p.y, y:p.x};
    case 2: return {x:-p.x, y:-p.y};
    case 3: return {x:p.y, y:-p.x};
  }
}

function roundRect(ctx, x, y, w, h, r){
  if (typeof r === 'number') r = {tl:r, tr:r, br:r, bl:r};
  ctx.beginPath();
  ctx.moveTo(x+r.tl, y);
  ctx.lineTo(x+w-r.tr, y);
  ctx.arcTo(x+w, y, x+w, y+r.tr, r.tr);
  ctx.lineTo(x+w, y+h-r.br);
  ctx.arcTo(x+w, y+h, x+w-r.br, y+h, r.br);
  ctx.lineTo(x+r.bl, y+h);
  ctx.arcTo(x, y+h, x, y+h-r.bl, r.bl);
  ctx.lineTo(x, y+r.tl);
  ctx.arcTo(x, y, x+r.tl, y, r.tl);
  ctx.closePath();
}

/* ============================================================
   2. COMPONENT LIBRARY
   Local coordinate system: grid units, origin = electrical center,
   +x right, +y down (canvas convention). Terminal span = 3 units
   for two-terminal parts unless noted. Rotation = quarter turns.
============================================================ */

// ---- resistor color-code table for realistic rendering ----
const RESISTOR_BANDS = [
  '#4a4a4a','#8b5a2b','#e2555a','#eab24d','#f5e663',
  '#6fc95a','#4a9ce0','#9a6fe0','#b0b0b0','#f4f1ea'
]; // 0..9 digit colors (black,brown,red,orange,yellow,green,blue,violet,grey,white)

function resistorBandColors(R){
  if (!(R > 0)) return ['#4a4a4a','#4a4a4a','#f4f1ea'];
  let exp = Math.floor(Math.log10(R));
  let mant = R / Math.pow(10, exp);
  // normalize to 2 significant digits
  let d1 = Math.floor(mant);
  let d2 = Math.round((mant - d1) * 10);
  if (d2 === 10){ d1++; d2 = 0; }
  if (d1 >= 10){ d1 = Math.floor(d1/10); exp++; }
  const multExp = exp - 1;
  const multColors = ['#4a4a4a','#8b5a2b','#e2555a','#eab24d','#f5e663','#6fc95a','#4a9ce0','#9a6fe0','#b0b0b0','#f4f1ea'];
  const multIdx = Math.max(0, Math.min(9, multExp+2));
  return [RESISTOR_BANDS[d1]||'#4a4a4a', RESISTOR_BANDS[d2]||'#4a4a4a', multColors[Math.max(0,Math.min(9,multExp))] || '#eab24d'];
}

const COMP = {}; // registry: type -> definition

function defComp(type, def){ COMP[type] = Object.assign({type}, def); }

/* ---------------- terminal helper ---------------- */
function twoTerm(span){ span = span || 3; return [
  {name:'a', x:-span/2, y:0},
  {name:'b', x: span/2, y:0}
]; }

/* ================= RESISTOR ================= */
defComp('resistor', {
  label:'Resistor', category:'Passive', icon:'R',
  terminals: twoTerm(3),
  params:{ resistance: 1000 },
  paramDefs:[{key:'resistance', label:'Resistance', unit:'Ω', type:'eng'}],
  drawSchematic(ctx,c,g){
    ctx.strokeStyle = c._stroke; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-1.05*g,0);
    const zig = [[-0.9,-0.4],[-0.6,0.4],[-0.3,-0.4],[0,0.4],[0.3,-0.4],[0.6,0.4],[0.9,-0.4]];
    ctx.lineTo(zig[0][0]*g, zig[0][1]*g);
    for (let i=1;i<zig.length;i++) ctx.lineTo(zig[i][0]*g, zig[i][1]*g);
    ctx.lineTo(1.05*g,0); ctx.lineTo(1.5*g,0);
    ctx.stroke();
    drawTermDots(ctx,c,g);
    drawValueLabel(ctx, c, g, fmtEng(c.params.resistance,'Ω'));
  },
  drawRealistic(ctx,c,g){
    const bw = 2.0*g, bh = 0.62*g;
    ctx.save();
    // leads
    ctx.strokeStyle = '#b8bcc4'; ctx.lineWidth = 2.4;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-bw/2,0); ctx.moveTo(bw/2,0); ctx.lineTo(1.5*g,0); ctx.stroke();
    // body
    const grad = ctx.createLinearGradient(0,-bh/2,0,bh/2);
    grad.addColorStop(0,'#e8cfa0'); grad.addColorStop(.5,'#d8b27c'); grad.addColorStop(1,'#c9975c');
    roundRect(ctx, -bw/2, -bh/2, bw, bh, bh/2.4);
    ctx.fillStyle = grad; ctx.fill();
    ctx.lineWidth = 1; ctx.strokeStyle = 'rgba(0,0,0,.25)'; ctx.stroke();
    // bands
    const bands = resistorBandColors(c.params.resistance);
    const bx = -bw/2 + bw*0.22;
    for (let i=0;i<3;i++){
      ctx.fillStyle = bands[i];
      ctx.fillRect(bx + i*bw*0.16, -bh/2+1, bw*0.09, bh-2);
    }
    ctx.restore();
    drawTermDots(ctx,c,g,true);
    drawValueLabel(ctx,c,g, fmtEng(c.params.resistance,'Ω'));
  }
});

/* ================= CAPACITOR ================= */
defComp('capacitor', {
  label:'Capacitor', category:'Passive', icon:'C',
  terminals: twoTerm(3),
  params:{ capacitance: 1e-6, ic: 0 },
  paramDefs:[
    {key:'capacitance', label:'Capacitance', unit:'F', type:'eng'},
    {key:'ic', label:'Initial Voltage', unit:'V', type:'eng'}
  ],
  drawSchematic(ctx,c,g){
    ctx.strokeStyle = c._stroke; ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.moveTo(-1.5*g,0); ctx.lineTo(-0.18*g,0);
    ctx.moveTo(0.18*g,0); ctx.lineTo(1.5*g,0);
    ctx.moveTo(-0.18*g,-0.6*g); ctx.lineTo(-0.18*g,0.6*g);
    ctx.moveTo(0.18*g,-0.6*g); ctx.lineTo(0.18*g,0.6*g);
    ctx.stroke();
    drawTermDots(ctx,c,g);
    drawValueLabel(ctx,c,g, fmtEng(c.params.capacitance,'F'));
  },
  drawRealistic(ctx,c,g){
    ctx.save();
    ctx.strokeStyle = '#b8bcc4'; ctx.lineWidth = 2.4;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-0.55*g,0); ctx.moveTo(0.55*g,0); ctx.lineTo(1.5*g,0); ctx.stroke();
    // electrolytic can
    const w = 1.1*g, h = 1.5*g;
    const grad = ctx.createLinearGradient(-w/2,0,w/2,0);
    grad.addColorStop(0,'#2c6ea8'); grad.addColorStop(.45,'#4a8fce'); grad.addColorStop(.55,'#3f81bd'); grad.addColorStop(1,'#1f5484');
    roundRect(ctx,-w/2,-h/2,w,h,4);
    ctx.fillStyle = grad; ctx.fill();
    ctx.fillStyle = 'rgba(255,255,255,.85)';
    ctx.fillRect(-w/2+2,-h/2+3, w*0.14, h-6);
    // top vent
    ctx.strokeStyle = 'rgba(255,255,255,.5)'; ctx.lineWidth = 1;
    ctx.beginPath(); ctx.moveTo(0,-h/2+3); ctx.lineTo(0,-h/2+9); ctx.moveTo(-3,-h/2+6); ctx.lineTo(3,-h/2+6); ctx.stroke();
    // minus stripe
    ctx.fillStyle = 'rgba(20,20,20,.55)';
    ctx.fillRect(-w/2, -h/2, w*0.32, h);
    ctx.fillStyle = '#e9ecf3'; ctx.font = (0.42*g)+'px var(--mono)'; ctx.textAlign='center'; ctx.textBaseline='middle';
    ctx.fillText('−', -w/2+w*0.16, 0);
    ctx.restore();
    drawTermDots(ctx,c,g,true);
    drawValueLabel(ctx,c,g, fmtEng(c.params.capacitance,'F'));
  }
});

/* ================= INDUCTOR ================= */
defComp('inductor', {
  label:'Inductor', category:'Passive', icon:'L',
  terminals: twoTerm(3),
  params:{ inductance: 0.01, ic: 0 },
  paramDefs:[
    {key:'inductance', label:'Inductance', unit:'H', type:'eng'},
    {key:'ic', label:'Initial Current', unit:'A', type:'eng'}
  ],
  drawSchematic(ctx,c,g){
    ctx.strokeStyle = c._stroke; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-0.9*g,0); ctx.stroke();
    for (let i=0;i<4;i++){
      const cx = (-0.9 + i*0.45)*g + 0.225*g;
      ctx.beginPath(); ctx.arc(cx, 0, 0.225*g, Math.PI, 0, false); ctx.stroke();
    }
    ctx.beginPath(); ctx.moveTo(0.9*g,0); ctx.lineTo(1.5*g,0); ctx.stroke();
    drawTermDots(ctx,c,g);
    drawValueLabel(ctx,c,g, fmtEng(c.params.inductance,'H'));
  },
  drawRealistic(ctx,c,g){
    ctx.save();
    ctx.strokeStyle = '#b8bcc4'; ctx.lineWidth = 2.4;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-1.0*g,0); ctx.moveTo(1.0*g,0); ctx.lineTo(1.5*g,0); ctx.stroke();
    // ferrite core body
    const w = 2.0*g, h = 0.7*g;
    const grad = ctx.createLinearGradient(0,-h/2,0,h/2);
    grad.addColorStop(0,'#4a4f5c'); grad.addColorStop(.5,'#2b2f38'); grad.addColorStop(1,'#1a1d24');
    roundRect(ctx,-w/2,-h/2,w,h,h/2); ctx.fillStyle = grad; ctx.fill();
    // copper windings
    ctx.strokeStyle = '#d9884a'; ctx.lineWidth = 2.6;
    for (let i=0;i<6;i++){
      const cx = -w/2 + (i+0.5)*(w/6);
      ctx.beginPath(); ctx.ellipse(cx,0, w/13, h/1.7, 0, 0, Math.PI*2); ctx.stroke();
    }
    ctx.restore();
    drawTermDots(ctx,c,g,true);
    drawValueLabel(ctx,c,g, fmtEng(c.params.inductance,'H'));
  }
});

/* ================= DC VOLTAGE SOURCE / BATTERY ================= */
defComp('battery', {
  label:'DC Source', category:'Sources', icon:'V',
  terminals: twoTerm(3),
  params:{ voltage: 5 },
  paramDefs:[{key:'voltage', label:'Voltage', unit:'V', type:'eng'}],
  drawSchematic(ctx,c,g){
    ctx.strokeStyle = c._stroke; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-0.55*g,0); ctx.moveTo(0.55*g,0); ctx.lineTo(1.5*g,0); ctx.stroke();
    ctx.lineWidth = 3; ctx.beginPath(); ctx.moveTo(-0.3*g,-0.55*g); ctx.lineTo(-0.3*g,0.55*g); ctx.stroke();
    ctx.lineWidth = 1.6; ctx.beginPath(); ctx.moveTo(0.3*g,-0.3*g); ctx.lineTo(0.3*g,0.3*g); ctx.stroke();
    ctx.fillStyle = c._stroke; ctx.font = (0.5*g)+'px var(--disp)'; ctx.textAlign='center';
    ctx.fillText('+', -0.68*g, -0.5*g);
    ctx.fillText('−', 0.68*g, -0.42*g);
    drawTermDots(ctx,c,g);
    drawValueLabel(ctx,c,g, fmtEng(c.params.voltage,'V'));
  },
  drawRealistic(ctx,c,g){
    ctx.save();
    ctx.strokeStyle = '#b8bcc4'; ctx.lineWidth = 2.4;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-0.95*g,0); ctx.moveTo(0.95*g,0); ctx.lineTo(1.5*g,0); ctx.stroke();
    const w = 1.9*g, h = 0.85*g;
    const grad = ctx.createLinearGradient(-w/2,0,w/2,0);
    grad.addColorStop(0,'#3a4048'); grad.addColorStop(.5,'#5a6272'); grad.addColorStop(1,'#2c3138');
    roundRect(ctx,-w/2,-h/2,w,h,4); ctx.fillStyle = grad; ctx.fill();
    // copper cap on + end
    ctx.fillStyle = '#cf9a52';
    roundRect(ctx, w/2-h*0.32, -h/2, h*0.32, h, {tl:0,bl:0,tr:4,br:4}); ctx.fill();
    ctx.fillStyle = '#e9ecf3'; ctx.font = 'bold '+(0.5*g)+'px var(--disp)'; ctx.textAlign='center'; ctx.textBaseline='middle';
    ctx.fillText('+', w/2-h*0.32-6, 0);
    ctx.fillText('−', -w/2+8, 0);
    ctx.restore();
    drawTermDots(ctx,c,g,true);
    drawValueLabel(ctx,c,g, fmtEng(c.params.voltage,'V'));
  }
});

/* ================= AC VOLTAGE SOURCE ================= */
defComp('acsource', {
  label:'AC Source', category:'Sources', icon:'~',
  terminals: twoTerm(3),
  params:{ amplitude: 5, frequency: 60, phase: 0, waveform: 'sine' },
  paramDefs:[
    {key:'waveform', label:'Waveform', type:'select', options:['sine','square','triangle','sawtooth']},
    {key:'amplitude', label:'Amplitude', unit:'V', type:'eng'},
    {key:'frequency', label:'Frequency', unit:'Hz', type:'eng'},
    {key:'phase', label:'Phase', unit:'deg', type:'eng'}
  ],
  drawSchematic(ctx,c,g){
    ctx.strokeStyle = c._stroke; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-0.6*g,0); ctx.moveTo(0.6*g,0); ctx.lineTo(1.5*g,0); ctx.stroke();
    ctx.beginPath(); ctx.arc(0,0,0.6*g,0,Math.PI*2); ctx.stroke();
    ctx.strokeStyle = c._stroke;
    drawWaveIcon(ctx, c.params.waveform||'sine', 0.34*g, 0.32*g);
    drawTermDots(ctx,c,g);
    drawValueLabel(ctx,c,g, fmtEng(c.params.amplitude,'V')+' @ '+fmtEng(c.params.frequency,'Hz')+' '+(c.params.waveform||'sine'));
  },
  drawRealistic(ctx,c,g){
    ctx.save();
    ctx.strokeStyle = '#b8bcc4'; ctx.lineWidth = 2.4;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-0.62*g,0); ctx.moveTo(0.62*g,0); ctx.lineTo(1.5*g,0); ctx.stroke();
    const grad = ctx.createRadialGradient(-0.15*g,-0.15*g,2,0,0,0.65*g);
    grad.addColorStop(0,'#3a4a5c'); grad.addColorStop(1,'#1c2530');
    ctx.beginPath(); ctx.arc(0,0,0.62*g,0,Math.PI*2); ctx.fillStyle = grad; ctx.fill();
    ctx.lineWidth = 1.5; ctx.strokeStyle = '#7f8ba0'; ctx.stroke();
    ctx.strokeStyle = '#35d0c0'; ctx.lineWidth = 2;
    drawWaveIcon(ctx, c.params.waveform||'sine', 0.36*g, 0.34*g);
    ctx.restore();
    drawTermDots(ctx,c,g,true);
    drawValueLabel(ctx,c,g, fmtEng(c.params.amplitude,'V')+' @ '+fmtEng(c.params.frequency,'Hz')+' '+(c.params.waveform||'sine'));
  }
});

/* ================= CURRENT SOURCE ================= */
defComp('currentsource', {
  label:'Current Src', category:'Sources', icon:'I',
  terminals: twoTerm(3),
  params:{ current: 0.01 },
  paramDefs:[{key:'current', label:'Current', unit:'A', type:'eng'}],
  drawSchematic(ctx,c,g){
    ctx.strokeStyle = c._stroke; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-0.6*g,0); ctx.moveTo(0.6*g,0); ctx.lineTo(1.5*g,0); ctx.stroke();
    ctx.beginPath(); ctx.arc(0,0,0.6*g,0,Math.PI*2); ctx.stroke();
    ctx.beginPath(); ctx.moveTo(-0.3*g,0); ctx.lineTo(0.3*g,0);
    ctx.moveTo(0.3*g,0); ctx.lineTo(0.12*g,-0.13*g); ctx.moveTo(0.3*g,0); ctx.lineTo(0.12*g,0.13*g);
    ctx.stroke();
    drawTermDots(ctx,c,g);
    drawValueLabel(ctx,c,g, fmtEng(c.params.current,'A'));
  },
  drawRealistic(ctx,c,g){
    ctx.save();
    ctx.strokeStyle = '#b8bcc4'; ctx.lineWidth = 2.4;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-0.62*g,0); ctx.moveTo(0.62*g,0); ctx.lineTo(1.5*g,0); ctx.stroke();
    const grad = ctx.createRadialGradient(-0.15*g,-0.15*g,2,0,0,0.65*g);
    grad.addColorStop(0,'#5c4a2e'); grad.addColorStop(1,'#2c2418');
    ctx.beginPath(); ctx.arc(0,0,0.62*g,0,Math.PI*2); ctx.fillStyle = grad; ctx.fill();
    ctx.lineWidth = 1.5; ctx.strokeStyle = '#c9975c'; ctx.stroke();
    ctx.strokeStyle = '#eab24d'; ctx.lineWidth = 2.4;
    ctx.beginPath(); ctx.moveTo(-0.32*g,0); ctx.lineTo(0.32*g,0);
    ctx.moveTo(0.32*g,0); ctx.lineTo(0.12*g,-0.15*g); ctx.moveTo(0.32*g,0); ctx.lineTo(0.12*g,0.15*g);
    ctx.stroke();
    ctx.restore();
    drawTermDots(ctx,c,g,true);
    drawValueLabel(ctx,c,g, fmtEng(c.params.current,'A'));
  }
});

/* ================= GROUND ================= */
defComp('ground', {
  label:'Ground', category:'Sources', icon:'⏚', single:true,
  terminals: [{name:'a', x:0, y:-1}],
  params:{},
  paramDefs:[],
  drawSchematic(ctx,c,g){
    ctx.strokeStyle = c._stroke; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(0,-1*g); ctx.lineTo(0,0); ctx.stroke();
    ctx.lineWidth = 2.2;
    [[0.5,0],[0.32,0.25],[0.14,0.5]].forEach(([w,y])=>{
      ctx.beginPath(); ctx.moveTo(-w*g, y*g); ctx.lineTo(w*g, y*g); ctx.stroke();
    });
    drawTermDots(ctx,c,g);
  },
  drawRealistic(ctx,c,g){
    ctx.strokeStyle = '#b8bcc4'; ctx.lineWidth = 2.4;
    ctx.beginPath(); ctx.moveTo(0,-1*g); ctx.lineTo(0,0); ctx.stroke();
    const grad = ctx.createLinearGradient(0,0,0,0.5*g);
    grad.addColorStop(0,'#7a8496'); grad.addColorStop(1,'#3d4453');
    ctx.fillStyle = grad;
    [[0.5,0,6],[0.32,0.22,5],[0.14,0.42,4]].forEach(([w,y,h])=>{
      ctx.fillRect(-w*g, y*g, w*2*g, h);
    });
    drawTermDots(ctx,c,g,true);
  }
});

/* ================= SWITCH ================= */
defComp('switch', {
  label:'Switch', category:'Control', icon:'/',
  terminals: twoTerm(3),
  params:{ closed: true },
  paramDefs:[{key:'closed', label:'Closed', type:'bool'}],
  drawSchematic(ctx,c,g){
    ctx.strokeStyle = c._stroke; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-0.6*g,0); ctx.moveTo(0.6*g,0); ctx.lineTo(1.5*g,0); ctx.stroke();
    ctx.beginPath(); ctx.arc(-0.6*g,0,2.6,0,Math.PI*2); ctx.fillStyle = c._stroke; ctx.fill();
    ctx.beginPath(); ctx.arc(0.6*g,0,2.6,0,Math.PI*2); ctx.fill();
    ctx.beginPath(); ctx.moveTo(-0.6*g,0);
    if (c.params.closed) ctx.lineTo(0.6*g,0); else ctx.lineTo(0.42*g,-0.42*g);
    ctx.stroke();
    drawTermDots(ctx,c,g);
    drawValueLabel(ctx,c,g, c.params.closed ? 'CLOSED' : 'OPEN');
  },
  drawRealistic(ctx,c,g){
    ctx.save();
    ctx.strokeStyle = '#b8bcc4'; ctx.lineWidth = 2.4;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-0.75*g,0); ctx.moveTo(0.75*g,0); ctx.lineTo(1.5*g,0); ctx.stroke();
    // toggle housing
    roundRect(ctx,-0.75*g,-0.4*g,1.5*g,0.8*g,6);
    ctx.fillStyle = '#2b2f38'; ctx.fill(); ctx.strokeStyle='rgba(0,0,0,.3)'; ctx.stroke();
    // lever
    ctx.strokeStyle = c.params.closed ? '#59c97a' : '#e2555a'; ctx.lineWidth = 4; ctx.lineCap='round';
    ctx.beginPath(); ctx.moveTo(0, 0.05*g);
    if (c.params.closed) ctx.lineTo(0,-0.32*g); else ctx.lineTo(0.3*g,-0.18*g);
    ctx.stroke();
    ctx.beginPath(); ctx.arc(0,0.05*g,3,0,Math.PI*2); ctx.fillStyle='#8a93a3'; ctx.fill();
    ctx.restore();
    drawTermDots(ctx,c,g,true);
    drawValueLabel(ctx,c,g, c.params.closed ? 'CLOSED' : 'OPEN');
  }
});

/* ================= DIODE ================= */
defComp('diode', {
  label:'Diode', category:'Semiconductor', icon:'▷|',
  terminals: twoTerm(3), // a = anode, b = cathode
  params:{ vf: 0.7 },
  paramDefs:[{key:'vf', label:'Forward Vf', unit:'V', type:'eng'}],
  drawSchematic(ctx,c,g){
    ctx.strokeStyle = c._stroke; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-0.45*g,0); ctx.moveTo(0.45*g,0); ctx.lineTo(1.5*g,0); ctx.stroke();
    ctx.beginPath(); ctx.moveTo(-0.45*g,-0.45*g); ctx.lineTo(-0.45*g,0.45*g); ctx.lineTo(0.35*g,0); ctx.closePath();
    ctx.fillStyle = c._stroke; ctx.fill();
    ctx.beginPath(); ctx.moveTo(0.35*g,-0.45*g); ctx.lineTo(0.35*g,0.45*g); ctx.stroke();
    drawTermDots(ctx,c,g);
    drawValueLabel(ctx,c,g, fmtEng(c.params.vf,'V')+' fwd');
  },
  drawRealistic(ctx,c,g){
    ctx.save();
    ctx.strokeStyle = '#b8bcc4'; ctx.lineWidth = 2.4;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-0.62*g,0); ctx.moveTo(0.62*g,0); ctx.lineTo(1.5*g,0); ctx.stroke();
    const w=1.24*g, h=0.5*g;
    const grad = ctx.createLinearGradient(0,-h/2,0,h/2);
    grad.addColorStop(0,'#3a3d44'); grad.addColorStop(.5,'#17181c'); grad.addColorStop(1,'#3a3d44');
    roundRect(ctx,-w/2,-h/2,w,h,h/2); ctx.fillStyle = grad; ctx.fill();
    ctx.fillStyle = '#dcdfe6'; ctx.fillRect(w/2-h*0.32,-h/2,h*0.22,h);
    ctx.restore();
    drawTermDots(ctx,c,g,true);
    drawValueLabel(ctx,c,g, fmtEng(c.params.vf,'V')+' fwd');
  }
});

/* ================= LED ================= */
defComp('led', {
  label:'LED', category:'Semiconductor', icon:'*',
  terminals: twoTerm(3),
  params:{ vf: 2.0, color:'#e2555a' },
  paramDefs:[
    {key:'vf', label:'Forward Vf', unit:'V', type:'eng'},
    {key:'color', label:'Color', type:'color'}
  ],
  drawSchematic(ctx,c,g){
    if (c._on){
      ctx.save();
      const glow = ctx.createRadialGradient(0,0,1,0,0,0.95*g);
      glow.addColorStop(0, c.params.color+'99'); glow.addColorStop(1, c.params.color+'00');
      ctx.beginPath(); ctx.arc(0,0,0.95*g,0,Math.PI*2); ctx.fillStyle = glow; ctx.fill();
      ctx.restore();
    }
    ctx.strokeStyle = c._stroke; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-0.45*g,0); ctx.moveTo(0.45*g,0); ctx.lineTo(1.5*g,0); ctx.stroke();
    ctx.beginPath(); ctx.moveTo(-0.45*g,-0.45*g); ctx.lineTo(-0.45*g,0.45*g); ctx.lineTo(0.35*g,0); ctx.closePath();
    ctx.fillStyle = c._on ? c.params.color : c._stroke; ctx.fill();
    ctx.beginPath(); ctx.moveTo(0.35*g,-0.45*g); ctx.lineTo(0.35*g,0.45*g); ctx.stroke();
    ctx.strokeStyle = c._on ? c.params.color : c._stroke; ctx.lineWidth = 1.4;
    for (const dx of [0.2,0.45]){
      ctx.beginPath(); ctx.moveTo(-0.1*g+dx*g,-0.55*g); ctx.lineTo(0.1*g+dx*g,-0.85*g);
      ctx.lineTo(0.02*g+dx*g,-0.78*g); ctx.moveTo(0.1*g+dx*g,-0.85*g); ctx.lineTo(0.02*g+dx*g,-0.72*g);
      ctx.stroke();
    }
    drawTermDots(ctx,c,g);
    drawValueLabel(ctx,c,g, c._on ? 'ON '+fmtEng(c._i||0,'A') : 'off');
  },
  drawRealistic(ctx,c,g){
    ctx.save();
    ctx.strokeStyle = '#b8bcc4'; ctx.lineWidth = 2.4;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-0.4*g,0.35*g); ctx.moveTo(0.4*g,0.35*g); ctx.lineTo(1.5*g,0.35*g); ctx.stroke();
    if (c._on){
      const glow = ctx.createRadialGradient(0,-0.05*g,1,0,-0.05*g,0.85*g);
      glow.addColorStop(0, c.params.color+'cc'); glow.addColorStop(1, c.params.color+'00');
      ctx.beginPath(); ctx.arc(0,-0.05*g,0.85*g,0,Math.PI*2); ctx.fillStyle = glow; ctx.fill();
    }
    // dome
    const domeGrad = ctx.createRadialGradient(-0.12*g,-0.25*g,1,0,-0.05*g,0.42*g);
    domeGrad.addColorStop(0, c._on ? '#ffffff' : 'rgba(255,255,255,.5)');
    domeGrad.addColorStop(0.35, c._on ? c.params.color : c.params.color+'55');
    domeGrad.addColorStop(1, c._on ? c.params.color : c.params.color+'22');
    ctx.beginPath(); ctx.arc(0,-0.05*g,0.4*g,Math.PI,0); ctx.lineTo(0.4*g,0.35*g); ctx.lineTo(-0.4*g,0.35*g); ctx.closePath();
    ctx.fillStyle = domeGrad; ctx.fill();
    ctx.lineWidth = 1; ctx.strokeStyle = 'rgba(0,0,0,.25)'; ctx.stroke();
    ctx.restore();
    drawTermDots(ctx,c,g,true);
    drawValueLabel(ctx,c,g, c._on ? 'ON '+fmtEng(c._i||0,'A') : 'off');
  }
});

/* ================= LAMP / BULB (resistive load) ================= */
defComp('lamp', {
  label:'Lamp', category:'Passive', icon:'◉',
  terminals: twoTerm(3),
  params:{ resistance: 100 },
  paramDefs:[{key:'resistance', label:'Resistance', unit:'Ω', type:'eng'}],
  drawSchematic(ctx,c,g){
    const p = Math.min(1, (c._p||0) / 0.5);
    if (p > 0.02){
      ctx.save();
      const glow = ctx.createRadialGradient(0,0,1,0,0,1.05*g);
      glow.addColorStop(0, `rgba(255,214,120,${0.15+0.55*p})`); glow.addColorStop(1,'rgba(255,214,120,0)');
      ctx.beginPath(); ctx.arc(0,0,1.05*g,0,Math.PI*2); ctx.fillStyle = glow; ctx.fill();
      ctx.restore();
    }
    ctx.strokeStyle = c._stroke; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-0.5*g,0); ctx.moveTo(0.5*g,0); ctx.lineTo(1.5*g,0); ctx.stroke();
    if (p > 0.02){ ctx.fillStyle = `rgba(255,214,120,${0.18+0.5*p})`; ctx.beginPath(); ctx.arc(0,0,0.5*g,0,Math.PI*2); ctx.fill(); }
    ctx.beginPath(); ctx.arc(0,0,0.5*g,0,Math.PI*2); ctx.stroke();
    ctx.strokeStyle = p > 0.02 ? '#ffdd88' : c._stroke;
    ctx.beginPath();
    ctx.moveTo(-0.35*g,-0.35*g); ctx.lineTo(0.35*g,0.35*g);
    ctx.moveTo(0.35*g,-0.35*g); ctx.lineTo(-0.35*g,0.35*g);
    ctx.stroke();
    drawTermDots(ctx,c,g);
    drawValueLabel(ctx,c,g, fmtEng(c.params.resistance,'Ω'));
  },
  drawRealistic(ctx,c,g){
    ctx.save();
    ctx.strokeStyle = '#b8bcc4'; ctx.lineWidth = 2.4;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0.55*g); ctx.lineTo(-0.28*g,0.55*g); ctx.moveTo(0.28*g,0.55*g); ctx.lineTo(1.5*g,0.55*g); ctx.stroke();
    const p = Math.min(1, (c._p||0) / 0.5); // power fraction for glow
    if (p > 0.02){
      const glow = ctx.createRadialGradient(0,-0.1*g,2,0,-0.1*g,0.9*g);
      glow.addColorStop(0, `rgba(255,214,120,${0.15+0.55*p})`); glow.addColorStop(1,'rgba(255,214,120,0)');
      ctx.beginPath(); ctx.arc(0,-0.1*g,0.9*g,0,Math.PI*2); ctx.fillStyle = glow; ctx.fill();
    }
    // glass bulb
    const bulbGrad = ctx.createRadialGradient(-0.15*g,-0.3*g,1,0,-0.1*g,0.52*g);
    bulbGrad.addColorStop(0,'rgba(255,255,255,.9)');
    bulbGrad.addColorStop(0.4, p>0.02 ? `rgba(255,${200-60*p},120,${0.5+0.4*p})` : 'rgba(220,225,235,.35)');
    bulbGrad.addColorStop(1, 'rgba(180,190,205,.18)');
    ctx.beginPath(); ctx.arc(0,-0.1*g,0.5*g,0,Math.PI*2); ctx.fillStyle = bulbGrad; ctx.fill();
    ctx.lineWidth = 1.2; ctx.strokeStyle = 'rgba(180,190,205,.55)'; ctx.stroke();
    // filament
    ctx.strokeStyle = p>0.02 ? '#ffdd88' : '#8a93a3'; ctx.lineWidth = 1.4;
    ctx.beginPath();
    ctx.moveTo(-0.18*g,0.1*g); ctx.lineTo(-0.1*g,-0.2*g); ctx.lineTo(0,0.05*g); ctx.lineTo(0.1*g,-0.2*g); ctx.lineTo(0.18*g,0.1*g);
    ctx.stroke();
    // base
    const baseGrad = ctx.createLinearGradient(0,0.15*g,0,0.55*g);
    baseGrad.addColorStop(0,'#9aa4b8'); baseGrad.addColorStop(1,'#5c6577');
    ctx.fillStyle = baseGrad;
    ctx.fillRect(-0.28*g,0.15*g,0.56*g,0.4*g);
    ctx.restore();
    drawTermDots(ctx,c,g,true);
    drawValueLabel(ctx,c,g, fmtEng(c.params.resistance,'Ω'));
  }
});

/* ================= POTENTIOMETER ================= */
defComp('potentiometer', {
  label:'Potentiometer', category:'Passive', icon:'Pot',
  terminals: [
    {name:'a', x:-1.5, y:0}, {name:'b', x:1.5, y:0}, {name:'w', x:0, y:-1.5}
  ],
  params:{ resistance: 10000, wiper: 0.5 },
  paramDefs:[
    {key:'resistance', label:'Total Resistance', unit:'Ω', type:'eng'},
    {key:'wiper', label:'Wiper Position', type:'slider', min:0, max:1, step:0.01}
  ],
  drawSchematic(ctx,c,g){
    ctx.strokeStyle = c._stroke; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-1.05*g,0);
    const zig = [[-0.9,-0.4],[-0.6,0.4],[-0.3,-0.4],[0,0.4],[0.3,-0.4],[0.6,0.4],[0.9,-0.4]];
    zig.forEach(p=>ctx.lineTo(p[0]*g,p[1]*g));
    ctx.lineTo(1.05*g,0); ctx.lineTo(1.5*g,0); ctx.stroke();
    // wiper arrow
    const wx = (-0.9 + 1.8*c.params.wiper)*g;
    ctx.beginPath(); ctx.moveTo(0,-1.5*g); ctx.lineTo(wx, -0.15*g); ctx.stroke();
    ctx.beginPath(); ctx.moveTo(wx,-0.15*g); ctx.lineTo(wx-4,-0.05*g); ctx.lineTo(wx+2,-0.02*g); ctx.closePath();
    ctx.fillStyle = c._stroke; ctx.fill();
    drawTermDots(ctx,c,g);
    drawValueLabel(ctx,c,g, fmtEng(c.params.resistance,'Ω')+' · '+Math.round(c.params.wiper*100)+'%');
  },
  drawRealistic(ctx,c,g){
    ctx.save();
    ctx.strokeStyle = '#b8bcc4'; ctx.lineWidth = 2.4;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-0.85*g,0); ctx.moveTo(0.85*g,0); ctx.lineTo(1.5*g,0);
    ctx.moveTo(0,-1.5*g); ctx.lineTo(0,-0.62*g); ctx.stroke();
    const grad = ctx.createLinearGradient(0,-0.55*g,0,0.55*g);
    grad.addColorStop(0,'#7a8496'); grad.addColorStop(1,'#3d4453');
    roundRect(ctx,-0.85*g,-0.55*g,1.7*g,1.1*g,6); ctx.fillStyle = grad; ctx.fill();
    ctx.strokeStyle='rgba(0,0,0,.3)'; ctx.stroke();
    // knob
    const kx = (-0.6 + 1.2*c.params.wiper)*g;
    ctx.beginPath(); ctx.arc(kx,0,0.16*g,0,Math.PI*2);
    ctx.fillStyle = '#eab24d'; ctx.fill();
    ctx.restore();
    drawTermDots(ctx,c,g,true);
    drawValueLabel(ctx,c,g, fmtEng(c.params.resistance,'Ω')+' · '+Math.round(c.params.wiper*100)+'%');
  }
});

/* ================= AMMETER (inline, 0-ohm branch) ================= */
defComp('ammeter', {
  label:'Ammeter', category:'Meters', icon:'A',
  terminals: twoTerm(3),
  params:{},
  paramDefs:[],
  drawSchematic(ctx,c,g){
    ctx.strokeStyle = c._stroke; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-0.6*g,0); ctx.moveTo(0.6*g,0); ctx.lineTo(1.5*g,0); ctx.stroke();
    ctx.beginPath(); ctx.arc(0,0,0.6*g,0,Math.PI*2); ctx.stroke();
    ctx.fillStyle = c._stroke; ctx.font=(0.6*g)+'px var(--mono)'; ctx.textAlign='center'; ctx.textBaseline='middle';
    ctx.fillText('A', 0, 2);
    drawTermDots(ctx,c,g);
    drawValueLabel(ctx,c,g, fmtEng(c._i||0,'A'));
  },
  drawRealistic(ctx,c,g){
    ctx.save();
    ctx.strokeStyle = '#b8bcc4'; ctx.lineWidth = 2.4;
    ctx.beginPath(); ctx.moveTo(-1.5*g,0); ctx.lineTo(-0.62*g,0); ctx.moveTo(0.62*g,0); ctx.lineTo(1.5*g,0); ctx.stroke();
    const grad = ctx.createRadialGradient(-0.1*g,-0.1*g,1,0,0,0.65*g);
    grad.addColorStop(0,'#3a4048'); grad.addColorStop(1,'#1c2027');
    ctx.beginPath(); ctx.arc(0,0,0.62*g,0,Math.PI*2); ctx.fillStyle = grad; ctx.fill();
    ctx.lineWidth=1.5; ctx.strokeStyle='#8a93a3'; ctx.stroke();
    ctx.fillStyle = '#35d0c0'; ctx.font='bold '+(0.5*g)+'px var(--mono)'; ctx.textAlign='center'; ctx.textBaseline='middle';
    ctx.fillText('A', 0, 1);
    ctx.restore();
    drawTermDots(ctx,c,g,true);
    drawValueLabel(ctx,c,g, fmtEng(c._i||0,'A'));
  }
});

const COMP_CATEGORIES = ['Sources','Passive','Semiconductor','Control','Meters'];

/* ============================================================
   shared draw helpers used by component drawSchematic/drawRealistic
============================================================ */
function drawTermDots(ctx, c, g, realistic){
  const def = COMP[c.type];
  ctx.fillStyle = realistic ? '#d9a25c' : c._stroke;
  def.terminals.forEach(t=>{
    ctx.beginPath();
    ctx.arc(t.x*g, t.y*g, realistic ? 2.6 : TERM_R*0.8, 0, Math.PI*2);
    ctx.fill();
  });
}

// small in-circle icon for the AC source showing which waveform
// shape (sine/square/triangle/sawtooth) it's currently generating —
// draws inside a box of half-width hw and half-height hh centered
// on the current canvas origin. Assumes ctx.strokeStyle/lineWidth
// are already set by the caller.
function drawWaveIcon(ctx, type, hw, hh){
  ctx.beginPath();
  if (type === 'square'){
    ctx.moveTo(-hw, hh);
    ctx.lineTo(-hw, -hh); ctx.lineTo(0, -hh); ctx.lineTo(0, hh); ctx.lineTo(hw, hh); ctx.lineTo(hw, -hh);
  } else if (type === 'triangle'){
    ctx.moveTo(-hw, 0);
    ctx.lineTo(-hw*0.5, -hh); ctx.lineTo(0, hh); ctx.lineTo(hw*0.5, -hh); ctx.lineTo(hw, 0);
  } else if (type === 'sawtooth'){
    ctx.moveTo(-hw, hh);
    ctx.lineTo(0, -hh); ctx.lineTo(0, hh); ctx.lineTo(hw, -hh);
  } else {
    ctx.moveTo(-hw, hh*0.4);
    ctx.bezierCurveTo(-hw*0.55, -hh, -hw*0.2, -hh, 0, 0);
    ctx.bezierCurveTo(hw*0.2, hh, hw*0.55, hh, hw, -hh*0.4);
  }
  ctx.stroke();
}

function drawValueLabel(ctx, c, g, text){
  if (!c._showLabel) return;
  ctx.save();
  ctx.rotate(-c.rotation * Math.PI/2); // keep text upright regardless of comp rotation
  ctx.fillStyle = state.theme === 'light' ? 'rgba(85,95,114,.95)' : 'rgba(154,164,184,.9)';
  ctx.font = '10.5px var(--mono)';
  ctx.textAlign = 'center'; ctx.textBaseline = 'top';
  ctx.fillText(text, 0, 0.95*g);
  if (c.label){
    ctx.fillStyle = state.theme === 'light' ? 'rgba(28,33,43,.95)' : 'rgba(233,236,243,.9)';
    ctx.fillText(c.label, 0, -1.35*g);
  }
  ctx.restore();
}

/* ============================================================
   3. CIRCUIT DATA MODEL
============================================================ */
class Circuit{
  constructor(){
    this.components = [];   // {id,type,x,y,rotation,params,label}
    this.wires = [];        // {id, x1,y1,x2,y2}
    this.nodeMap = null;    // computed by extractNodes()
    this.groundNetId = null;
  }
  clear(){ this.components = []; this.wires = []; this.nodeMap = null; }

  addComponent(type, x, y, rotation, params){
    const def = COMP[type];
    const comp = {
      id: uid('u'), type, x: snap(x), y: snap(y), rotation: rotation||0,
      params: Object.assign({}, def.params, params||{}),
      label: '', _showLabel: true,
    };
    this.components.push(comp);
    return comp;
  }
  removeComponent(id){
    this.components = this.components.filter(c=>c.id!==id);
  }
  addWire(x1,y1,x2,y2){
    if (x1===x2 && y1===y2) return null;
    const w = {id: uid('w'), x1,y1,x2,y2};
    this.wires.push(w);
    return w;
  }
  removeWire(id){ this.wires = this.wires.filter(w=>w.id!==id); }

  // absolute terminal position of a component's terminal index
  termPos(comp, idx){
    const def = COMP[comp.type];
    const t = def.terminals[idx];
    const r = rotPt({x:t.x, y:t.y}, comp.rotation);
    return {x: comp.x + r.x, y: comp.y + r.y};
  }
  allTerms(comp){
    const def = COMP[comp.type];
    return def.terminals.map((t,i)=>({idx:i, name:t.name, pos:this.termPos(comp,i)}));
  }

  componentAt(px, py, g){ // px,py in grid units; hit-test bounding radius
    for (let i=this.components.length-1;i>=0;i--){
      const c = this.components[i];
      const dx = px-c.x, dy = py-c.y;
      const local = rotPt({x:dx,y:dy}, -c.rotation);
      if (Math.abs(local.x) <= 1.6 && Math.abs(local.y) <= 0.9) return c;
    }
    return null;
  }
  terminalNear(px, py, tolGrid){
    tolGrid = tolGrid || 0.35;
    let best=null, bestD=tolGrid;
    for (const c of this.components){
      const terms = this.allTerms(c);
      for (const t of terms){
        const d = Math.hypot(t.pos.x-px, t.pos.y-py);
        if (d < bestD){ bestD=d; best={comp:c, idx:t.idx, pos:t.pos}; }
      }
    }
    return best;
  }
  wireEndpointNear(px,py,tolGrid){
    tolGrid = tolGrid || 0.3;
    let best=null, bestD=tolGrid;
    for (const w of this.wires){
      for (const [x,y] of [[w.x1,w.y1],[w.x2,w.y2]]){
        const d = Math.hypot(x-px,y-py);
        if (d<bestD){ bestD=d; best={x,y}; }
      }
    }
    return best;
  }

  // distance from point to a wire segment, in grid units
  wireAt(px, py, tolGrid){
    tolGrid = tolGrid || 0.22;
    let best=null, bestD=tolGrid;
    for (const w of this.wires){
      const d = pointToSegmentDist(px,py, w.x1,w.y1, w.x2,w.y2);
      if (d < bestD){ bestD=d; best=w; }
    }
    return best;
  }

  toJSON(){
    return JSON.stringify({
      components: this.components.map(c=>({id:c.id,type:c.type,x:c.x,y:c.y,rotation:c.rotation,params:c.params,label:c.label})),
      wires: this.wires.map(w=>({id:w.id,x1:w.x1,y1:w.y1,x2:w.x2,y2:w.y2}))
    }, null, 1);
  }
  fromJSON(json){
    const data = typeof json==='string' ? JSON.parse(json) : json;
    this.clear();
    (data.components||[]).forEach(c=>{
      this.components.push(Object.assign({_showLabel:true, label:''}, c));
    });
    (data.wires||[]).forEach(w=> this.wires.push(Object.assign({}, w)));
    let maxId = 0;
    [...this.components, ...this.wires].forEach(o=>{
      const m = String(o.id).match(/\d+$/); if (m) maxId = Math.max(maxId, parseInt(m[0]));
    });
    state.nextId = maxId+1;
  }
}

function pointToSegmentDist(px,py, x1,y1,x2,y2){
  const dx = x2-x1, dy = y2-y1;
  const lenSq = dx*dx+dy*dy;
  if (lenSq < 1e-9) return Math.hypot(px-x1,py-y1);
  let t = ((px-x1)*dx + (py-y1)*dy) / lenSq;
  t = Math.max(0, Math.min(1, t));
  const cx = x1+t*dx, cy = y1+t*dy;
  return Math.hypot(px-cx, py-cy);
}

const circuit = new Circuit();

/* ============================================================
   4. NETLIST / NODE EXTRACTION
   Grid-snapped coordinates mean electrically-connected points
   share exact (x,y). We union wire endpoints and let identical
   coordinates merge naturally via a coordinate-keyed union-find.
============================================================ */
class UnionFind{
  constructor(){ this.parent = new Map(); }
  find(k){
    if (!this.parent.has(k)) this.parent.set(k,k);
    let root = k;
    while (this.parent.get(root) !== root) root = this.parent.get(root);
    // path compression
    let cur = k;
    while (this.parent.get(cur) !== root){ const next = this.parent.get(cur); this.parent.set(cur, root); cur = next; }
    return root;
  }
  union(a,b){ const ra=this.find(a), rb=this.find(b); if (ra!==rb) this.parent.set(ra, rb); }
}

function extractNodes(circ){
  const uf = new UnionFind();
  // seed every terminal & wire endpoint so isolated points exist as their own set
  circ.components.forEach(c=>{
    circ.allTerms(c).forEach(t=> uf.find(pointKey(t.pos)));
  });
  circ.wires.forEach(w=>{
    const ka = pointKey({x:w.x1,y:w.y1}), kb = pointKey({x:w.x2,y:w.y2});
    uf.union(ka, kb);
  });

  // find ground root(s)
  let groundRoot = null;
  circ.components.forEach(c=>{
    if (c.type === 'ground'){
      const p = circ.termPos(c, 0);
      groundRoot = uf.find(pointKey(p));
    }
  });

  const rootToNode = new Map();
  if (groundRoot !== null) rootToNode.set(groundRoot, 0);
  let nextNode = 1;
  const termNode = new Map(); // "compId:termIdx" -> node number

  circ.components.forEach(c=>{
    circ.allTerms(c).forEach(t=>{
      const root = uf.find(pointKey(t.pos));
      if (!rootToNode.has(root)) rootToNode.set(root, nextNode++);
      termNode.set(c.id+':'+t.idx, rootToNode.get(root));
    });
  });

  return {
    termNode,
    hasGround: groundRoot !== null,
    numNodes: new Set([...rootToNode.values(), 0]).size,
  };
}

function nodeOf(nodeInfo, compId, termIdx){
  return nodeInfo.termNode.get(compId+':'+termIdx) ?? 0;
}

function buildNetlistText(circ){
  const info = extractNodes(circ);
  if (!info.hasGround){
    return '* ⚠ No ground reference placed.\n* Add a Ground component to solve the circuit.';
  }
  let lines = ['* Voltra netlist — auto-generated', '* Node 0 = GND', ''];
  circ.components.forEach(c=>{
    if (c.type === 'ground') return;
    const def = COMP[c.type];
    const nodes = def.terminals.map((t,i)=>'n'+nodeOf(info,c.id,i));
    let valueStr = '';
    switch(c.type){
      case 'resistor': valueStr = c.params.resistance+''; break;
      case 'lamp': valueStr = c.params.resistance+' (lamp)'; break;
      case 'capacitor': valueStr = c.params.capacitance+''; break;
      case 'inductor': valueStr = c.params.inductance+''; break;
      case 'battery': valueStr = 'DC '+c.params.voltage; break;
      case 'acsource': valueStr = (c.params.waveform||'SIN').toUpperCase()+' 0 '+c.params.amplitude+' '+c.params.frequency; break;
      case 'currentsource': valueStr = 'DC '+c.params.current; break;
      case 'switch': valueStr = c.params.closed ? 'R=0.01 (closed)' : 'R=10Meg (open)'; break;
      case 'diode': valueStr = 'VF='+c.params.vf; break;
      case 'led': valueStr = 'VF='+c.params.vf; break;
      case 'potentiometer': valueStr = c.params.resistance+' wiper='+c.params.wiper; break;
      case 'ammeter': valueStr = '0V (probe)'; break;
    }
    const prefix = {resistor:'R',lamp:'R',capacitor:'C',inductor:'L',battery:'V',acsource:'V',
      currentsource:'I',switch:'S',diode:'D',led:'D',potentiometer:'RV',ammeter:'AM'}[c.type] || 'X';
    lines.push(prefix + c.id.replace(/\D/g,'') + '  ' + nodes.join(' ') + '  ' + valueStr);
  });
  lines.push('', '.op', '.end');
  return lines.join('\n');
}

/* ============================================================
   5 & 6. MNA SOLVER + DC / TRANSIENT SIMULATION ENGINE
   A compact Modified-Nodal-Analysis engine in the spirit of
   ngspice's own approach: linear stamps for passive parts and
   sources, Norton companion models for C/L under backward-Euler
   integration, and Newton-Raphson linearization for diodes using
   SPICE-style voltage limiting so forward/reverse switching (as
   in a bridge rectifier) converges correctly within a timestep.
============================================================ */
const sim = {
  info: null,
  branches: [],     // list of {kind:'vsource'|'inductor'|'ammeter', comp}
  size: 0,
  nodeCount: 0,
  // persistent state across timesteps
  capV: {},          // comp.id -> previous voltage (a-b)
  indI: {},          // comp.id -> previous current (a->b)
  diodeV: {},        // comp.id -> last linearization voltage guess
  lastResult: null,
};

function prepareSim(circ){
  const info = extractNodes(circ);
  sim.info = info;
  sim.nodeCount = new Set([...info.termNode.values()]).size; // includes node 0 if present
  const n = Math.max(0, sim.nodeCount - (info.hasGround?1:0));
  sim.branches = [];
  circ.components.forEach(c=>{
    if (c.type==='battery' || c.type==='acsource' || c.type==='ammeter'){
      sim.branches.push({kind:'vsource', comp:c});
    }
  });
  sim.branchIndex = {};
  sim.branches.forEach((b,i)=> sim.branchIndex[b.comp.id]=i);
  sim.n = n;
  return info;
}

// solves one linear/linearized pass. dynamic = null for pure-resistive DC (C open, L short).
// dynamic = {dt, useCompanion:true} for transient step (uses capV/indI/diodeV state).
function assembleAndSolve(circ, dynamic, diodeGuess){
  const info = sim.info;
  if (!info.hasGround) return null;
  const n = sim.n;
  // inductor branches only exist as unknowns during transient (companion model); during pure DC treat inductor as short (0V source, extra unknown)
  const indBranches = [];
  if (dynamic){
    circ.components.forEach(c=>{ if (c.type==='inductor') indBranches.push(c); });
  } else {
    circ.components.forEach(c=>{ if (c.type==='inductor') indBranches.push(c); }); // shorted -> also needs branch (0V) for DC op
  }
  const totalBranches = sim.branches.length + indBranches.length;
  const size = n + totalBranches;
  const G = Array.from({length:size}, ()=> new Array(size).fill(0));
  const z = new Array(size).fill(0);

  function stampG(a,b,g){
    if (a>0){ G[a-1][a-1]+=g; }
    if (b>0){ G[b-1][b-1]+=g; }
    if (a>0 && b>0){ G[a-1][b-1]-=g; G[b-1][a-1]-=g; }
  }
  function stampI(from,to,I){ // current I flows from 'from' node to 'to' node through the element
    if (from>0) z[from-1]-=I;
    if (to>0) z[to-1]+=I;
  }
  function branchRowFor(idx){ return n+idx; }
  function stampBranchVsource(a,b,idx,V){
    const row = branchRowFor(idx);
    if (a>0){ G[row][a-1]=1; G[a-1][row]+=1; }
    if (b>0){ G[row][b-1]=-1; G[b-1][row]-=1; }
    z[row]=V;
  }

  circ.components.forEach(c=>{
    const nA = nodeOf(info,c.id,0);
    switch(c.type){
      case 'resistor': {
        const R = Math.max(1e-6, parseEng(c.params.resistance));
        stampG(nA, nodeOf(info,c.id,1), 1/R);
        break;
      }
      case 'lamp': {
        const R = Math.max(1e-6, parseEng(c.params.resistance));
        stampG(nA, nodeOf(info,c.id,1), 1/R);
        break;
      }
      case 'potentiometer': {
        const R = Math.max(1, parseEng(c.params.resistance));
        const w = Math.min(0.98, Math.max(0.02, c.params.wiper));
        const ra = R*w, rb = R*(1-w);
        const nB = nodeOf(info,c.id,1), nW = nodeOf(info,c.id,2);
        stampG(nA,nW,1/ra); stampG(nW,nB,1/rb);
        break;
      }
      case 'switch': {
        const R = c.params.closed ? 0.01 : 1e7;
        stampG(nA, nodeOf(info,c.id,1), 1/R);
        break;
      }
      case 'currentsource': {
        stampI(nA, nodeOf(info,c.id,1), parseEng(c.params.current));
        break;
      }
      case 'battery': {
        const idx = sim.branchIndex[c.id];
        stampBranchVsource(nA, nodeOf(info,c.id,1), idx, parseEng(c.params.voltage));
        break;
      }
      case 'acsource': {
        const idx = sim.branchIndex[c.id];
        const t = dynamic ? state.t : 0;
        const v = acWaveformValue(
          c.params.waveform || 'sine',
          parseEng(c.params.amplitude),
          parseEng(c.params.frequency),
          c.params.phase || 0,
          t
        );
        stampBranchVsource(nA, nodeOf(info,c.id,1), idx, v);
        break;
      }
      case 'ammeter': {
        const idx = sim.branchIndex[c.id];
        stampBranchVsource(nA, nodeOf(info,c.id,1), idx, 0);
        break;
      }
      case 'capacitor': {
        const nB = nodeOf(info,c.id,1);
        const Cap = Math.max(1e-15, parseEng(c.params.capacitance));
        if (dynamic){
          const geq = Cap/dynamic.dt;
          const vprev = sim.capV[c.id] ?? (parseEng(c.params.ic)||0);
          const ieq = geq*vprev;
          stampG(nA,nB,geq);
          stampI(nB,nA,ieq); // supplies current into nA, out of nB
        } // else: open circuit for pure DC op-point -> no stamp
        break;
      }
      case 'inductor': {
        const nB = nodeOf(info,c.id,1);
        const Lh = Math.max(1e-12, parseEng(c.params.inductance));
        const idx = sim.branches.length + indBranches.indexOf(c);
        const row = branchRowFor(idx);
        if (nA>0) { G[row][nA-1]=1; G[nA-1][row]+=1; }
        if (nB>0) { G[row][nB-1]=-1; G[nB-1][row]-=1; }
        if (dynamic){
          const Leq = Lh/dynamic.dt;
          const iprev = sim.indI[c.id] ?? (parseEng(c.params.ic)||0);
          G[row][row] = -Leq;
          z[row] = -Leq*iprev;
        } else {
          // DC operating point: inductor = short (0V)
          G[row][row] = 0;
          z[row] = 0;
        }
        break;
      }
      case 'diode': case 'led': {
        const nB = nodeOf(info,c.id,1);
        // --- SPICE-style diode companion model ---
        // Shockley equation I = Is*(exp(V/nVt)-1). Is is fixed tiny
        // (real diode leakage scale); the ideality/emission scaling
        // (nVt) is derived per-component so that its own Vf lines up
        // with a realistic ~20mA forward operating point. Gmin (a
        // small parallel conductance) is always present for matrix
        // conditioning, exactly as SPICE does — it's far too small
        // to compromise blocking behavior (1e-12 S ~ 1 TΩ).
        const Vt = 0.02585;                       // thermal voltage @ ~300K
        const Vf = Math.max(0.05, c.params.vf || 0.7);
        const Is = 1e-14;
        const Gmin = 1e-12;
        const nEmis = Math.max(1, Vf / (Vt * Math.log(0.02/Is + 1)));
        const nVt = nEmis * Vt;

        // linearization point, carried over from the previous NR
        // iteration / timestep (defaults to 0V — unbiased — the
        // first time a diode is ever evaluated)
        let Vg = (diodeGuess && diodeGuess[c.id] !== undefined) ? diodeGuess[c.id] : (sim.diodeV[c.id] ?? 0);

        // SPICE voltage limiting: only clamps *forward* excursions
        // (where exp() would otherwise blow up numerically). Reverse
        // excursions are left completely unclamped — a diode needs
        // to be able to swing many volts negative within a single
        // Newton step (e.g. at the peak of an AC half-cycle in a
        // bridge rectifier) in order to actually shut off in time.
        const Vcrit = nVt * Math.log(nVt / (Math.SQRT2 * Is));
        if (Vg > Vcrit){
          Vg = Vcrit + nVt * Math.log(1 + (Vg - Vcrit) / nVt);
        }
        Vg = Math.min(Vg, Vf * 4); // generous absolute forward ceiling

        const ex = Math.exp(Math.min(60, Vg / nVt));
        const Id = Is * (ex - 1);
        const gd = (Is / nVt) * ex;      // exponential (diode) conductance
        const geq = gd + Gmin;           // total companion conductance
        const ieq = Id - gd * Vg;        // companion current source (Gmin cancels out)

        stampG(nA, nB, geq);
        stampI(nB, nA, -ieq);
        break;
      }
      default: break;
    }
  });

  const x = solveLinear(G, z);
  const V = new Array(sim.nodeCount).fill(0);
  for (let i=1;i<=n;i++) V[i] = x[i-1];
  const branchI = {};
  sim.branches.forEach((b,i)=> branchI[b.comp.id] = x[n+i]);
  indBranches.forEach((c,i)=> branchI[c.id] = x[n+sim.branches.length+i]);
  return {V, branchI, indBranches};
}

function nodeVoltage(V, node){ return node===0 ? 0 : (V[node]||0); }

function solveDCOperatingPoint(circ){
  prepareSim(circ);
  if (!sim.info.hasGround) return null;
  let result = null, diodeGuess = {};
  for (let iter=0; iter<60; iter++){
    result = assembleAndSolve(circ, null, diodeGuess);
    if (!result) return null;
    let maxDelta = 0;
    circ.components.forEach(c=>{
      if (c.type==='diode' || c.type==='led'){
        const nA = nodeOf(sim.info,c.id,0), nB = nodeOf(sim.info,c.id,1);
        const v = nodeVoltage(result.V,nA) - nodeVoltage(result.V,nB);
        const prev = diodeGuess[c.id] ?? (sim.diodeV[c.id] ?? 0);
        maxDelta = Math.max(maxDelta, Math.abs(v-prev));
        // full Newton step: the internal Vcrit-based limiting inside
        // assembleAndSolve already keeps the exponential well-behaved,
        // so no additional per-iteration damping is needed here.
        diodeGuess[c.id] = v;
      }
    });
    if (maxDelta < 1e-7) break;
  }
  circ.components.forEach(c=>{
    if (c.type==='diode' || c.type==='led') sim.diodeV[c.id] = diodeGuess[c.id];
  });
  return result;
}

function stepTransient(circ, dt){
  if (!sim.info || !sim.info.hasGround) prepareSim(circ);
  if (!sim.info.hasGround) return null;
  let result=null, diodeGuess={};
  for (let iter=0; iter<40; iter++){
    result = assembleAndSolve(circ, {dt}, diodeGuess);
    if (!result) return null;
    let maxDelta=0;
    circ.components.forEach(c=>{
      if (c.type==='diode' || c.type==='led'){
        const nA = nodeOf(sim.info,c.id,0), nB = nodeOf(sim.info,c.id,1);
        const v = nodeVoltage(result.V,nA)-nodeVoltage(result.V,nB);
        const prev = diodeGuess[c.id] ?? (sim.diodeV[c.id] ?? 0);
        maxDelta = Math.max(maxDelta, Math.abs(v-prev));
        diodeGuess[c.id] = v;
      }
    });
    if (maxDelta < 1e-6) break;
  }
  // commit companion state for next step
  circ.components.forEach(c=>{
    if (c.type==='capacitor'){
      const nA=nodeOf(sim.info,c.id,0), nB=nodeOf(sim.info,c.id,1);
      sim.capV[c.id] = nodeVoltage(result.V,nA)-nodeVoltage(result.V,nB);
    }
    if (c.type==='inductor'){
      sim.indI[c.id] = result.branchI[c.id] || 0;
    }
    if (c.type==='diode' || c.type==='led'){
      sim.diodeV[c.id] = diodeGuess[c.id] ?? sim.diodeV[c.id];
    }
  });
  return result;
}

/* ============================================================
   7. RENDERING PIPELINE
============================================================ */
const canvases = {
  grid: document.getElementById('gridcanvas'),
  wire: document.getElementById('wirecanvas'),
  comp: document.getElementById('compcanvas'),
  overlay: document.getElementById('overlaycanvas'),
};
const ctxs = {};
Object.keys(canvases).forEach(k => ctxs[k] = canvases[k].getContext('2d'));
const stageWrap = document.getElementById('stage-wrap');

function resizeCanvases(){
  const w = stageWrap.clientWidth, h = stageWrap.clientHeight;
  const dpr = window.devicePixelRatio || 1;
  Object.values(canvases).forEach(cv=>{
    cv.width = w*dpr; cv.height = h*dpr; cv.style.width = w+'px'; cv.style.height = h+'px';
  });
  Object.values(ctxs).forEach(c=> c.setTransform(dpr,0,0,dpr,0,0));
  renderAll();
}

function worldToScreen(x,y){ // x,y in grid units
  return { x: x*GRID*state.zoom + state.pan.x, y: y*GRID*state.zoom + state.pan.y };
}
function screenToWorld(x,y){
  return { x: (x-state.pan.x)/(GRID*state.zoom), y: (y-state.pan.y)/(GRID*state.zoom) };
}

function renderGrid(){
  const ctx = ctxs.grid;
  const w = stageWrap.clientWidth, h = stageWrap.clientHeight;
  const tc = themeColors();
  ctx.clearRect(0,0,w,h);
  ctx.fillStyle = tc.bg; ctx.fillRect(0,0,w,h);
  const step = GRID*state.zoom;
  if (step < 4) return;
  const ox = state.pan.x % step, oy = state.pan.y % step;
  ctx.fillStyle = tc.gridDot;
  const rad = state.zoom < 0.6 ? 0.6 : 1.1;
  for (let x = ox; x < w; x += step){
    for (let y = oy; y < h; y += step){
      ctx.beginPath(); ctx.arc(x,y,rad,0,Math.PI*2); ctx.fill();
    }
  }
  // major lines every 5 cells
  ctx.strokeStyle = tc.gridLine; ctx.lineWidth = 1;
  const majorStep = step*5;
  const mox = state.pan.x % majorStep, moy = state.pan.y % majorStep;
  ctx.beginPath();
  for (let x = mox; x < w; x += majorStep){ ctx.moveTo(x,0); ctx.lineTo(x,h); }
  for (let y = moy; y < h; y += majorStep){ ctx.moveTo(0,y); ctx.lineTo(w,y); }
  ctx.stroke();
}

function currentFlowOffset(){
  return (state.t * 60) % 16; // dash animation phase
}

function renderWires(){
  const ctx = ctxs.wire;
  const w = stageWrap.clientWidth, h = stageWrap.clientHeight;
  ctx.clearRect(0,0,w,h);
  const g = GRID*state.zoom;
  const tc = themeColors();
  circuit.wires.forEach(wire=>{
    const p1 = worldToScreen(wire.x1, wire.y1), p2 = worldToScreen(wire.x2, wire.y2);
    ctx.lineCap = 'round';
    const isSel = state.wireSelection.has(wire.id);
    if (state.view === 'realistic'){
      ctx.strokeStyle = '#8a5a2e'; ctx.lineWidth = 4.4;
      ctx.beginPath(); ctx.moveTo(p1.x,p1.y); ctx.lineTo(p2.x,p2.y); ctx.stroke();
      ctx.strokeStyle = isSel ? '#35d0c0' : '#d9a25c'; ctx.lineWidth = 2.2;
      ctx.beginPath(); ctx.moveTo(p1.x,p1.y); ctx.lineTo(p2.x,p2.y); ctx.stroke();
    } else {
      ctx.strokeStyle = isSel ? '#35d0c0' : tc.wire; ctx.lineWidth = isSel ? 3 : 2;
      ctx.beginPath(); ctx.moveTo(p1.x,p1.y); ctx.lineTo(p2.x,p2.y); ctx.stroke();
    }
    if (state.running && wire._current){
      ctx.save();
      ctx.strokeStyle = '#35d0c0'; ctx.lineWidth = 2.2;
      ctx.setLineDash([6,10]);
      ctx.lineDashOffset = -currentFlowOffset() * Math.sign(wire._current);
      ctx.beginPath(); ctx.moveTo(p1.x,p1.y); ctx.lineTo(p2.x,p2.y); ctx.stroke();
      ctx.restore();
    }
    // junction dot if 3+ connections share an endpoint
    [[wire.x1,wire.y1],[wire.x2,wire.y2]].forEach(([x,y])=>{
      let count = 0;
      circuit.wires.forEach(w2=>{ if ((w2.x1===x&&w2.y1===y)||(w2.x2===x&&w2.y2===y)) count++; });
      if (count > 1){
        const p = worldToScreen(x,y);
        ctx.beginPath(); ctx.arc(p.x,p.y, state.view==='realistic'?3.6:3.2, 0, Math.PI*2);
        ctx.fillStyle = state.view==='realistic' ? '#d9a25c' : tc.junction; ctx.fill();
      }
    });
  });
  // wire draft preview
  if (state.wireDraft){
    const p1 = worldToScreen(state.wireDraft.from.x, state.wireDraft.from.y);
    const p2 = worldToScreen(state.wireDraft.to.x, state.wireDraft.to.y);
    ctx.strokeStyle = '#35d0c0'; ctx.lineWidth = 2; ctx.setLineDash([5,4]);
    ctx.beginPath(); ctx.moveTo(p1.x,p1.y); ctx.lineTo(p2.x,p2.y); ctx.stroke();
    ctx.setLineDash([]);
  }
}

function renderComponents(){
  const ctx = ctxs.comp;
  const w = stageWrap.clientWidth, h = stageWrap.clientHeight;
  ctx.clearRect(0,0,w,h);
  const g = GRID*state.zoom;
  const tc = themeColors();
  circuit.components.forEach(c=>{
    const p = worldToScreen(c.x, c.y);
    ctx.save();
    ctx.translate(p.x, p.y);
    ctx.rotate(c.rotation * Math.PI/2);
    c._stroke = state.selection.has(c.id) ? '#35d0c0' : tc.compStroke;
    const def = COMP[c.type];
    if (state.selection.has(c.id)){
      ctx.save();
      ctx.rotate(0);
      ctx.fillStyle = 'rgba(53,208,192,0.08)';
      ctx.beginPath(); ctx.arc(0,0, 1.55*g, 0, Math.PI*2); ctx.fill();
      ctx.restore();
    }
    try{
      if (state.view === 'realistic' && def.drawRealistic) def.drawRealistic(ctx, c, g);
      else def.drawSchematic(ctx, c, g);
    }catch(e){ /* fail soft per component */ }
    ctx.restore();
  });
}

function renderOverlay(){
  const ctx = ctxs.overlay;
  const w = stageWrap.clientWidth, h = stageWrap.clientHeight;
  ctx.clearRect(0,0,w,h);
  const g = GRID*state.zoom;
  // hovered terminal highlight
  if (state.hoverTerm){
    const p = worldToScreen(state.hoverTerm.pos.x, state.hoverTerm.pos.y);
    ctx.beginPath(); ctx.arc(p.x,p.y,7,0,Math.PI*2);
    ctx.strokeStyle = '#35d0c0'; ctx.lineWidth = 2; ctx.stroke();
  }
  // probes
  state.probes.forEach(pr=>{
    const pa = worldToScreen(pr.a.x, pr.a.y);
    ctx.beginPath(); ctx.arc(pa.x,pa.y,5,0,Math.PI*2);
    ctx.fillStyle = pr.color || '#eab24d'; ctx.fill();
    ctx.strokeStyle = '#12151b'; ctx.lineWidth = 1.5; ctx.stroke();
    if (pr.b){
      const pb = worldToScreen(pr.b.x, pr.b.y);
      ctx.beginPath(); ctx.arc(pb.x,pb.y,5,0,Math.PI*2); ctx.fillStyle = pr.color||'#eab24d'; ctx.fill(); ctx.stroke();
      ctx.setLineDash([3,3]); ctx.strokeStyle = pr.color||'#eab24d'; ctx.lineWidth=1;
      ctx.beginPath(); ctx.moveTo(pa.x,pa.y); ctx.lineTo(pb.x,pb.y); ctx.stroke(); ctx.setLineDash([]);
    }
  });
  // marquee selection box
  if (state.dragging && state.dragging.type==='marquee'){
    const a = worldToScreen(state.dragging.x0, state.dragging.y0);
    const b = worldToScreen(state.dragging.x1, state.dragging.y1);
    ctx.fillStyle = 'rgba(53,208,192,0.08)'; ctx.strokeStyle = '#35d0c0'; ctx.lineWidth = 1;
    const x = Math.min(a.x,b.x), y = Math.min(a.y,b.y);
    ctx.fillRect(x,y, Math.abs(b.x-a.x), Math.abs(b.y-a.y));
    ctx.strokeRect(x,y, Math.abs(b.x-a.x), Math.abs(b.y-a.y));
  }
  // ghost placement preview
  if (state.dragging && state.dragging.type==='place-ghost'){
    const d = state.dragging;
    const p = worldToScreen(d.x, d.y);
    ctx.save(); ctx.translate(p.x,p.y); ctx.rotate((d.rotation||0)*Math.PI/2); ctx.globalAlpha = 0.55;
    const def = COMP[d.compType];
    const fake = {type:d.compType, params:Object.assign({},def.params), rotation:0, _stroke:'#35d0c0', _showLabel:false};
    try{ def.drawSchematic(ctx, fake, g); }catch(e){}
    ctx.restore();
  }
}

function renderAll(){
  renderGrid(); renderWires(); renderComponents(); renderOverlay();
  document.getElementById('zoomreadout').textContent = Math.round(state.zoom*100)+'%';
}

/* ============================================================
   8a. PALETTE CONSTRUCTION
============================================================ */
function buildPalette(filter){
  const root = document.getElementById('palette-root');
  root.innerHTML = '';
  const f = (filter||'').toLowerCase();
  const tc = themeColors();
  COMP_CATEGORIES.forEach(cat=>{
    const items = Object.values(COMP).filter(d=>d.category===cat && d.label.toLowerCase().includes(f));
    if (!items.length) return;
    const catEl = document.createElement('div');
    catEl.className = 'pcat';
    catEl.innerHTML = `<div class="pcat-head"><span>${cat}</span><span class="chev">▾</span></div><div class="pcat-body"></div>`;
    catEl.querySelector('.pcat-head').addEventListener('click', ()=> catEl.classList.toggle('collapsed'));
    const body = catEl.querySelector('.pcat-body');
    items.forEach(def=>{
      const partEl = document.createElement('div');
      partEl.className = 'part'; partEl.draggable = true;
      partEl.dataset.type = def.type;
      const cv = document.createElement('canvas'); cv.width=64; cv.height=44;
      const pctx = cv.getContext('2d');
      pctx.translate(32,22); pctx.scale(1,1);
      const fake = {type:def.type, params:Object.assign({},def.params), rotation:0, _stroke:tc.compStroke, _showLabel:false};
      try{
        if (state.view==='realistic' && def.drawRealistic) def.drawRealistic(pctx, fake, 13);
        else def.drawSchematic(pctx, fake, 13);
      }catch(e){}
      partEl.appendChild(cv);
      const lbl = document.createElement('span'); lbl.textContent = def.label; partEl.appendChild(lbl);
      partEl.addEventListener('dragstart', ev=>{
        ev.dataTransfer.setData('text/plain', def.type);
        ev.dataTransfer.effectAllowed = 'copy';
      });
      // touch/click-to-place fallback for environments without HTML5 drag support
      partEl.addEventListener('click', ()=>{
        state.pendingPlace = def.type;
        toast('Click on the grid to place a ' + def.label);
        log('Click the canvas to place ' + def.label);
      });
      body.appendChild(partEl);
    });
    root.appendChild(catEl);
  });
}
document.getElementById('partsearch').addEventListener('input', e=> buildPalette(e.target.value));

/* ============================================================
   8b. STAGE INTERACTION — drag-drop placement
============================================================ */
stageWrap.addEventListener('dragover', e=>{ e.preventDefault(); e.dataTransfer.dropEffect='copy'; });
stageWrap.addEventListener('drop', e=>{
  e.preventDefault();
  const type = e.dataTransfer.getData('text/plain');
  if (!type || !COMP[type]) return;
  const rect = stageWrap.getBoundingClientRect();
  const wpt = screenToWorld(e.clientX-rect.left, e.clientY-rect.top);
  const comp = circuit.addComponent(type, snap(wpt.x), snap(wpt.y), 0);
  selectOnly(comp.id);
  log('Placed ' + COMP[type].label, 'ok');
  renderAll(); refreshNetlist();
});

/* mouse state */
let mouse = {x:0,y:0,down:false,wx:0,wy:0};

function clientToWorld(e){
  const rect = stageWrap.getBoundingClientRect();
  const sx = e.clientX-rect.left, sy = e.clientY-rect.top;
  return Object.assign(screenToWorld(sx,sy), {sx,sy});
}

function selectOnly(id){ state.selection.clear(); state.wireSelection.clear(); if (id) state.selection.add(id); updatePropsPanel(); }
function toggleSelect(id){ if (state.selection.has(id)) state.selection.delete(id); else state.selection.add(id); updatePropsPanel(); }
function selectWireOnly(id){ state.selection.clear(); state.wireSelection.clear(); if (id) state.wireSelection.add(id); updatePropsPanel(); }
function toggleWireSelect(id){ if (state.wireSelection.has(id)) state.wireSelection.delete(id); else state.wireSelection.add(id); updatePropsPanel(); }
function clearSelection(){ state.selection.clear(); state.wireSelection.clear(); updatePropsPanel(); }

stageWrap.addEventListener('mousedown', e=>{
  const w = clientToWorld(e);
  mouse.down = true; mouse.wx = w.x; mouse.wy = w.y;

  // click-to-place fallback (used by the palette item click handler)
  if (state.pendingPlace){
    const type = state.pendingPlace;
    state.pendingPlace = null;
    if (COMP[type]){
      const comp = circuit.addComponent(type, snap(w.x), snap(w.y), 0);
      selectOnly(comp.id);
      log('Placed ' + COMP[type].label, 'ok');
      renderAll(); refreshNetlist();
    }
    return;
  }

  if (e.button === 1 || (e.button===0 && e.altKey)){
    state.dragging = {type:'pan', startX:e.clientX, startY:e.clientY, panX:state.pan.x, panY:state.pan.y};
    stageWrap.classList.add('panning');
    return;
  }

  if (state.tool === 'wire'){
    const term = circuit.terminalNear(w.x, w.y) || circuit.wireEndpointNear(w.x,w.y);
    const startPt = term ? (term.pos||term) : {x:snap(w.x), y:snap(w.y)};
    state.wireDraft = {from:startPt, to:startPt};
    return;
  }

  if (state.tool === 'probe'){
    const term = circuit.terminalNear(w.x, w.y, 0.5);
    if (term){
      const colors = ['#eab24d','#35d0c0','#e2555a','#9a6fe0'];
      const pr = {id:uid('p'), a:term.pos, color: colors[state.probes.length % colors.length]};
      state.probes.push(pr);
      renderMeters();
      renderAll();
    }
    return;
  }

  if (state.tool === 'delete'){
    const hitC = circuit.componentAt(w.x,w.y);
    if (hitC){ circuit.removeComponent(hitC.id); log('Deleted '+COMP[hitC.type].label,'warn'); renderAll(); refreshNetlist(); return; }
    const hitW = circuit.wireAt(w.x,w.y);
    if (hitW){ circuit.removeWire(hitW.id); log('Deleted wire','warn'); renderAll(); refreshNetlist(); return; }
    return;
  }

  // select tool
  const hitComp = circuit.componentAt(w.x, w.y);
  if (hitComp){
    if (!state.selection.has(hitComp.id) && !e.shiftKey) selectOnly(hitComp.id);
    else if (e.shiftKey) toggleSelect(hitComp.id);
    state.dragging = {
      type:'move-components',
      ids: [...state.selection],
      startWX: w.x, startWY: w.y,
      origins: [...state.selection].map(id=>{ const c=circuit.components.find(cc=>cc.id===id); return {id, x:c.x, y:c.y}; })
    };
    return;
  }
  const hitWire = circuit.wireAt(w.x, w.y);
  if (hitWire){
    if (!state.wireSelection.has(hitWire.id) && !e.shiftKey) selectWireOnly(hitWire.id);
    else if (e.shiftKey) toggleWireSelect(hitWire.id);
    else selectWireOnly(hitWire.id);
    renderAll();
    return;
  }
  if (!e.shiftKey) clearSelection();
  state.dragging = {type:'marquee', x0:w.x, y0:w.y, x1:w.x, y1:w.y};
});

window.addEventListener('mousemove', e=>{
  const w = clientToWorld(e);
  document.getElementById('coordread').textContent = 'x:'+w.x.toFixed(2)+'  y:'+w.y.toFixed(2);

  if (state.tool === 'select' || state.tool==='wire'){
    state.hoverTerm = circuit.terminalNear(w.x, w.y, 0.4);
  }

  if (state.wireDraft){
    const term = circuit.terminalNear(w.x, w.y, 0.4) || circuit.wireEndpointNear(w.x, w.y, 0.3);
    state.wireDraft.to = term ? (term.pos || term) : {x: snap(w.x), y: snap(w.y)};
    renderWires();
  }

  if (!state.dragging){ renderOverlay(); return; }

  if (state.dragging.type === 'pan'){
    state.pan.x = state.dragging.panX + (e.clientX-state.dragging.startX);
    state.pan.y = state.dragging.panY + (e.clientY-state.dragging.startY);
    renderAll();
    return;
  }
  if (state.dragging.type === 'move-components'){
    const dx = snap(w.x - state.dragging.startWX), dy = snap(w.y - state.dragging.startWY);
    state.dragging.origins.forEach(o=>{
      const c = circuit.components.find(cc=>cc.id===o.id);
      if (c){ c.x = snap(o.x+dx); c.y = snap(o.y+dy); }
    });
    renderAll();
    return;
  }
  if (state.dragging.type === 'marquee'){
    state.dragging.x1 = w.x; state.dragging.y1 = w.y;
    renderOverlay();
    return;
  }
});

window.addEventListener('mouseup', e=>{
  if (state.dragging && state.dragging.type === 'pan'){ stageWrap.classList.remove('panning'); state.dragging=null; return; }
  if (state.dragging && state.dragging.type === 'move-components'){
    state.dragging = null; refreshNetlist(); return;
  }
  if (state.dragging && state.dragging.type === 'marquee'){
    const {x0,y0,x1,y1} = state.dragging;
    const minx=Math.min(x0,x1), maxx=Math.max(x0,x1), miny=Math.min(y0,y1), maxy=Math.max(y0,y1);
    circuit.components.forEach(c=>{
      if (c.x>=minx && c.x<=maxx && c.y>=miny && c.y<=maxy) state.selection.add(c.id);
    });
    state.dragging = null; updatePropsPanel(); renderAll(); return;
  }
  if (state.wireDraft){
    const from = state.wireDraft.from, to = state.wireDraft.to;
    if (from.x !== to.x || from.y !== to.y){
      // orthogonal routing: horizontal then vertical
      if (from.x !== to.x && from.y !== to.y){
        circuit.addWire(from.x, from.y, to.x, from.y);
        circuit.addWire(to.x, from.y, to.x, to.y);
      } else {
        circuit.addWire(from.x, from.y, to.x, to.y);
      }
      log('Wire added', 'ok');
      refreshNetlist();
    }
    state.wireDraft = null;
    renderAll();
  }
  mouse.down = false;
});

stageWrap.addEventListener('wheel', e=>{
  e.preventDefault();
  const rect = stageWrap.getBoundingClientRect();
  const sx = e.clientX-rect.left, sy = e.clientY-rect.top;
  const before = screenToWorld(sx,sy);
  const factor = e.deltaY < 0 ? 1.1 : 0.9;
  state.zoom = Math.min(4, Math.max(0.25, state.zoom*factor));
  const after = worldToScreen(before.x, before.y);
  state.pan.x += sx-after.x; state.pan.y += sy-after.y;
  renderAll();
}, {passive:false});

stageWrap.addEventListener('contextmenu', e=>{
  e.preventDefault();
  const w = clientToWorld(e);
  const hit = circuit.componentAt(w.x,w.y);
  if (hit){
    if (!state.selection.has(hit.id)) selectOnly(hit.id);
    openCtxMenu(e.clientX, e.clientY);
    return;
  }
  const hitWire = circuit.wireAt(w.x,w.y);
  if (hitWire){
    if (!state.wireSelection.has(hitWire.id)) selectWireOnly(hitWire.id);
    renderAll();
    openCtxMenu(e.clientX, e.clientY);
  }
});

function openCtxMenu(x,y){
  const m = document.getElementById('ctxmenu');
  const isWireOnly = state.wireSelection.size>0 && state.selection.size===0;
  m.querySelectorAll('#ctx-rotate,#ctx-flip,#ctx-dup').forEach(el=> el.style.display = isWireOnly ? 'none' : 'flex');
  m.style.left = x+'px'; m.style.top = y+'px'; m.style.display='block';
}
window.addEventListener('click', e=>{
  if (!e.target.closest('#ctxmenu')) document.getElementById('ctxmenu').style.display='none';
});
document.getElementById('ctx-rotate').addEventListener('click', ()=> rotateSelection());
document.getElementById('ctx-flip').addEventListener('click', ()=> rotateSelection());
document.getElementById('ctx-dup').addEventListener('click', ()=> duplicateSelection());
document.getElementById('ctx-delete').addEventListener('click', ()=> deleteSelection());

function rotateSelection(){
  state.selection.forEach(id=>{
    const c = circuit.components.find(cc=>cc.id===id);
    if (c) c.rotation = (c.rotation+1)%4;
  });
  renderAll(); refreshNetlist();
}
function duplicateSelection(){
  const newIds = [];
  state.selection.forEach(id=>{
    const c = circuit.components.find(cc=>cc.id===id);
    if (c){
      const nc = circuit.addComponent(c.type, c.x+2, c.y+2, c.rotation, Object.assign({},c.params));
      newIds.push(nc.id);
    }
  });
  state.selection = new Set(newIds);
  renderAll(); updatePropsPanel(); refreshNetlist();
}
function deleteSelection(){
  state.selection.forEach(id=> circuit.removeComponent(id));
  state.wireSelection.forEach(id=> circuit.removeWire(id));
  state.selection.clear();
  state.wireSelection.clear();
  updatePropsPanel(); renderAll(); refreshNetlist();
}

/* ============================================================
   8c. KEYBOARD SHORTCUTS
============================================================ */
window.addEventListener('keydown', e=>{
  if (e.target.tagName==='INPUT' || e.target.tagName==='SELECT') return;
  if (e.code === 'Space'){ e.preventDefault(); toggleRun(); }
  else if (e.key==='r' || e.key==='R'){ rotateSelection(); }
  else if (e.key==='Delete' || e.key==='Backspace'){ deleteSelection(); }
  else if (e.key==='v' || e.key==='V'){ setTool('select'); }
  else if (e.key==='w' || e.key==='W'){ setTool('wire'); }
  else if (e.key==='p' || e.key==='P'){ setTool('probe'); }
  else if ((e.metaKey||e.ctrlKey) && e.key==='d'){ e.preventDefault(); duplicateSelection(); }
  else if ((e.metaKey||e.ctrlKey) && e.key==='s'){ e.preventDefault(); saveCircuit(); }
  else if (e.key==='Escape'){ clearSelection(); state.wireDraft=null; state.pendingPlace=null; renderAll(); }
});

function setTool(tool){
  state.tool = tool;
  ['select','wire','probe','delete'].forEach(t=>{
    document.getElementById('st-'+t).classList.toggle('active', t===tool);
  });
}
document.getElementById('st-select').addEventListener('click', ()=>setTool('select'));
document.getElementById('st-wire').addEventListener('click', ()=>setTool('wire'));
document.getElementById('st-probe').addEventListener('click', ()=>setTool('probe'));
document.getElementById('st-delete').addEventListener('click', ()=>setTool('delete'));

/* ============================================================
   9. RIGHT PANEL — properties / netlist / console tabs
============================================================ */
document.querySelectorAll('.rp-tab').forEach(tab=>{
  tab.addEventListener('click', ()=>{
    document.querySelectorAll('.rp-tab').forEach(t=>t.classList.remove('active'));
    document.querySelectorAll('.rp-pane').forEach(p=>p.classList.remove('active'));
    tab.classList.add('active');
    document.getElementById(tab.dataset.pane).classList.add('active');
    if (tab.dataset.pane === 'pane-netlist') refreshNetlist();
  });
});

function updatePropsPanel(){
  const empty = document.getElementById('prop-empty');
  const content = document.getElementById('prop-content');
  const ids = [...state.selection];

  if (ids.length === 0 && state.wireSelection.size > 0){
    empty.classList.add('hidden'); content.classList.remove('hidden');
    const n = state.wireSelection.size;
    content.innerHTML = `<div class="prop-title"><span class="swatch" style="background:var(--teal)"></span>${n} wire${n>1?'s':''} selected</div>
    <div class="prop-sub">Click Delete or press Del to remove.</div>
    <div class="btnrow"><button class="tbtn ghost" onclick="deleteSelection()" style="color:var(--red)">🗑 Delete wire${n>1?'s':''}</button></div>`;
    return;
  }

  if (ids.length !== 1){
    empty.classList.remove('hidden'); content.classList.add('hidden');
    if (ids.length > 1){ empty.classList.add('hidden'); content.classList.remove('hidden');
      content.innerHTML = `<div class="prop-title"><span class="swatch"></span>${ids.length} components selected</div>
      <div class="prop-sub">Rotate, duplicate, or delete as a group.</div>
      <div class="btnrow">
        <button class="tbtn ghost" onclick="rotateSelection()">Rotate</button>
        <button class="tbtn ghost" onclick="duplicateSelection()">Duplicate</button>
        <button class="tbtn ghost" onclick="deleteSelection()" style="color:var(--red)">Delete</button>
      </div>`;
    }
    return;
  }
  const c = circuit.components.find(cc=>cc.id===ids[0]);
  if (!c){ empty.classList.remove('hidden'); content.classList.add('hidden'); return; }
  empty.classList.add('hidden'); content.classList.remove('hidden');
  const def = COMP[c.type];

  let html = `<div class="prop-title"><span class="swatch"></span>${def.label}</div>
  <div class="prop-sub">${c.id} · rot ${c.rotation*90}°</div>`;

  html += `<div class="field"><label>Label</label><input type="text" id="f-label" value="${escapeHtml(c.label||'')}" placeholder="optional name"></div>`;

  def.paramDefs.forEach(pd=>{
    const val = c.params[pd.key];
    if (pd.type === 'eng'){
      html += `<div class="field"><label>${pd.label}</label><div class="row">
        <input type="text" data-key="${pd.key}" class="pf-eng" value="${val}">
        <div class="unit">${pd.unit}</div>
      </div></div>`;
    } else if (pd.type === 'bool'){
      html += `<div class="checkrow"><input type="checkbox" data-key="${pd.key}" class="pf-bool" ${val?'checked':''}><label>${pd.label}</label></div>`;
    } else if (pd.type === 'slider'){
      html += `<div class="field"><label>${pd.label} <span class="rangeval" id="rv-${pd.key}">${Math.round(val*100)}%</span></label>
        <input type="range" data-key="${pd.key}" class="pf-slider" min="${pd.min}" max="${pd.max}" step="${pd.step}" value="${val}"></div>`;
    } else if (pd.type === 'color'){
      html += `<div class="field"><label>${pd.label}</label><input type="color" data-key="${pd.key}" class="pf-color" value="${val}" style="height:34px;padding:2px;"></div>`;
    } else if (pd.type === 'select'){
      const curVal = (val === undefined || val === null) ? pd.options[0] : val;
      html += `<div class="field"><label>${pd.label}</label><select data-key="${pd.key}" class="pf-select">
        ${pd.options.map(o=>`<option value="${o}" ${o===curVal?'selected':''}>${o.charAt(0).toUpperCase()+o.slice(1)}</option>`).join('')}
      </select></div>`;
    }
  });

  html += `<div class="readouts" id="prop-readouts"></div>
  <div class="btnrow" style="margin-top:14px;">
    <button class="tbtn ghost" onclick="rotateSelection()">↻ Rotate</button>
    <button class="tbtn ghost" onclick="duplicateSelection()">⧉ Duplicate</button>
  </div>
  <div class="btnrow"><button class="tbtn ghost" onclick="deleteSelection()" style="color:var(--red)">🗑 Delete</button></div>`;

  content.innerHTML = html;

  const labelInput = document.getElementById('f-label');
  labelInput.addEventListener('input', ()=>{ c.label = labelInput.value; renderAll(); });

  content.querySelectorAll('.pf-eng').forEach(inp=>{
    inp.addEventListener('change', ()=>{
      c.params[inp.dataset.key] = parseEng(inp.value);
      renderAll(); refreshNetlist();
    });
  });
  content.querySelectorAll('.pf-bool').forEach(inp=>{
    inp.addEventListener('change', ()=>{
      c.params[inp.dataset.key] = inp.checked;
      renderAll(); refreshNetlist();
    });
  });
  content.querySelectorAll('.pf-slider').forEach(inp=>{
    inp.addEventListener('input', ()=>{
      c.params[inp.dataset.key] = parseFloat(inp.value);
      document.getElementById('rv-'+inp.dataset.key).textContent = Math.round(inp.value*100)+'%';
      renderAll();
    });
  });
  content.querySelectorAll('.pf-color').forEach(inp=>{
    inp.addEventListener('input', ()=>{ c.params[inp.dataset.key] = inp.value; renderAll(); });
  });
  content.querySelectorAll('.pf-select').forEach(inp=>{
    inp.addEventListener('change', ()=>{
      c.params[inp.dataset.key] = inp.value;
      renderAll(); refreshNetlist();
    });
  });

  updatePropReadouts(c);
}

function updatePropReadouts(c){
  const el = document.getElementById('prop-readouts');
  if (!el) return;
  if (!sim.lastResult || !sim.info){ el.innerHTML=''; return; }
  const nA = nodeOf(sim.info, c.id, 0);
  const nB = COMP[c.type].terminals.length>1 ? nodeOf(sim.info, c.id, 1) : null;
  const vA = nodeVoltage(sim.lastResult.V, nA);
  const vB = nB!==null ? nodeVoltage(sim.lastResult.V, nB) : 0;
  const vDrop = nB!==null ? (vA-vB) : vA;
  const ibranch = sim.lastResult.branchI ? sim.lastResult.branchI[c.id] : undefined;
  let current = ibranch;
  if (current === undefined && nB!==null && c.params.resistance){
    current = vDrop / Math.max(1e-9, parseEng(c.params.resistance));
  }
  el.innerHTML = `
    <div class="readout"><div class="rl">Voltage</div><div class="rv hot">${fmtEng(vDrop,'V')}</div></div>
    <div class="readout"><div class="rl">Current</div><div class="rv hot">${current!==undefined?fmtEng(current,'A'):'—'}</div></div>
  `;
}

/* ============================================================
   NETLIST TAB
============================================================ */
function refreshNetlist(){
  document.getElementById('netlist-out').textContent = buildNetlistText(circuit);
}
document.getElementById('btn-netlist-refresh').addEventListener('click', refreshNetlist);
document.getElementById('btn-netlist-copy').addEventListener('click', ()=>{
  const text = document.getElementById('netlist-out').textContent;
  navigator.clipboard?.writeText(text).then(()=> toast('Netlist copied')).catch(()=>{});
});

/* ============================================================
   10. RUN LOOP, OSCILLOSCOPE & LIVE METERS
============================================================ */
const scopeCanvas = document.getElementById('scopecanvas');
const scopeCtx = scopeCanvas.getContext('2d');
const SCOPE_WINDOW = 0.05; // seconds shown on screen

function resizeScope(){
  const wrap = document.getElementById('scope-wrap');
  const w = wrap.clientWidth, h = wrap.clientHeight;
  const dpr = window.devicePixelRatio||1;
  scopeCanvas.width = w*dpr; scopeCanvas.height = h*dpr;
  scopeCanvas.style.width = w+'px'; scopeCanvas.style.height = h+'px';
  scopeCtx.setTransform(dpr,0,0,dpr,0,0);
}

function setSimStatus(text, live){
  document.getElementById('simstat-text').textContent = text;
  document.getElementById('simstat').classList.toggle('live', !!live);
}

function toggleRun(){ state.running ? stopSim() : startSim(); }

function startSim(){
  prepareSim(circuit);
  if (!sim.info.hasGround){
    toast('Add a ground symbol before running the simulation.', 'err');
    log('Cannot run: circuit has no ground reference.', 'err');
    return;
  }
  // reset dynamic state & seed from a DC operating point
  sim.capV = {}; sim.indI = {}; sim.diodeV = {};
  circuit.components.forEach(c=>{
    if (c.type==='capacitor') sim.capV[c.id] = parseEng(c.params.ic)||0;
    if (c.type==='inductor') sim.indI[c.id] = parseEng(c.params.ic)||0;
  });
  state.t = 0;
  state.history = {t:[], series:{}};
  state.running = true;
  document.getElementById('btn-run').innerHTML = '<svg viewBox="0 0 24 24" fill="currentColor"><rect x="6" y="5" width="4" height="14"/><rect x="14" y="5" width="4" height="14"/></svg>Stop';
  document.getElementById('btn-run').classList.add('danger-run');
  setSimStatus('running', true);
  log('Simulation started', 'ok');
  runStep();
}
function stopSim(){
  state.running = false;
  if (state.runTimer) cancelAnimationFrame(state.runTimer);
  document.getElementById('btn-run').innerHTML = '<svg viewBox="0 0 24 24" fill="currentColor"><path d="M8 5v14l11-7z"/></svg>Run';
  document.getElementById('btn-run').classList.remove('danger-run');
  setSimStatus('idle', false);
  log('Simulation stopped');
}

let lastFrameTime = 0;
function runStep(ts){
  if (!state.running) return;
  const stepsPerFrame = Math.max(1, Math.round(6 * state.simSpeed));
  for (let s=0; s<stepsPerFrame; s++){
    const result = stepTransient(circuit, state.dt);
    if (!result){ stopSim(); toast('Solver failed — check circuit topology','err'); return; }
    sim.lastResult = result;
    state.t += state.dt;
    recordHistory(result);
    updateComponentDynamicFlags(result);
  }
  updateWireCurrents();
  renderComponents(); renderWires();
  renderScope();
  renderMeters();
  if ([...state.selection].length===1) updatePropReadouts(circuit.components.find(c=>state.selection.has(c.id)));
  state.runTimer = requestAnimationFrame(runStep);
}

function recordHistory(result){
  state.history.t.push(state.t);
  circuit.components.forEach(c=>{
    if (c.type==='battery'||c.type==='acsource'||c.type==='capacitor'||c.type==='resistor'||c.type==='lamp'){
      const nA = nodeOf(sim.info,c.id,0), nB = COMP[c.type].terminals.length>1?nodeOf(sim.info,c.id,1):null;
      const v = nodeVoltage(result.V,nA) - (nB!==null?nodeVoltage(result.V,nB):0);
      if (!state.history.series[c.id]) state.history.series[c.id] = [];
      state.history.series[c.id].push(v);
    }
  });
  state.probes.forEach(pr=>{
    const term = circuit.terminalNear(pr.a.x, pr.a.y, 0.5);
    if (term){
      const node = nodeOf(sim.info, term.comp.id, term.idx);
      const v = nodeVoltage(result.V, node);
      if (!state.history.series['probe:'+pr.id]) state.history.series['probe:'+pr.id]=[];
      state.history.series['probe:'+pr.id].push(v);
    }
  });
  const maxSamples = Math.ceil(SCOPE_WINDOW/state.dt)+5;
  if (state.history.t.length > maxSamples*3){
    state.history.t.splice(0, state.history.t.length-maxSamples*2);
    Object.keys(state.history.series).forEach(k=>{
      state.history.series[k].splice(0, state.history.series[k].length-maxSamples*2);
    });
  }
}

function updateComponentDynamicFlags(result){
  circuit.components.forEach(c=>{
    if (c.type==='led'){
      const nA=nodeOf(sim.info,c.id,0), nB=nodeOf(sim.info,c.id,1);
      const v = nodeVoltage(result.V,nA)-nodeVoltage(result.V,nB);
      const R = Math.max(1,(v)/0.001);
      c._on = v > (c.params.vf*0.6);
      c._i = Math.max(0, v>0 ? v/1000 : 0);
    }
    if (c.type==='lamp'){
      const nA=nodeOf(sim.info,c.id,0), nB=nodeOf(sim.info,c.id,1);
      const v = nodeVoltage(result.V,nA)-nodeVoltage(result.V,nB);
      const Rr = Math.max(1e-6,parseEng(c.params.resistance));
      c._p = (v*v)/Rr;
    }
    if (c.type==='ammeter'){ c._i = result.branchI[c.id]||0; }
  });
}

function updateWireCurrents(){
  // approximate: mark wires touching a component with nonzero current as "carrying current"
  circuit.wires.forEach(w=> w._current = 0);
  circuit.components.forEach(c=>{
    let cur = sim.lastResult.branchI ? sim.lastResult.branchI[c.id] : undefined;
    if (cur === undefined) return;
    const p0 = circuit.termPos(c,0);
    circuit.wires.forEach(w=>{
      if ((w.x1===p0.x&&w.y1===p0.y)||(w.x2===p0.x&&w.y2===p0.y)) w._current = cur;
    });
  });
}

function renderScope(){
  const w = scopeCanvas.clientWidth, h = scopeCanvas.clientHeight;
  const tc = themeColors();
  scopeCtx.clearRect(0,0,w,h);
  scopeCtx.fillStyle = tc.bg; scopeCtx.fillRect(0,0,w,h);
  // grid
  scopeCtx.strokeStyle = tc.gridDot; scopeCtx.lineWidth = 1;
  scopeCtx.beginPath();
  for (let x=0;x<=w;x+=w/10){ scopeCtx.moveTo(x,0); scopeCtx.lineTo(x,h); }
  for (let y=0;y<=h;y+=h/8){ scopeCtx.moveTo(0,y); scopeCtx.lineTo(w,y); }
  scopeCtx.stroke();
  scopeCtx.strokeStyle = tc.gridLine;
  scopeCtx.beginPath(); scopeCtx.moveTo(0,h/2); scopeCtx.lineTo(w,h/2); scopeCtx.stroke();

  const keys = Object.keys(state.history.series);
  if (!keys.length || !state.history.t.length){ drawScopeIdle(w,h); return; }
  const tArr = state.history.t;
  const tEnd = tArr[tArr.length-1];
  const tStart = tEnd - SCOPE_WINDOW;
  let i0 = tArr.findIndex(t=>t>=tStart); if (i0<0) i0=0;

  // determine autoscale across visible window
  let vmax = 0.001;
  keys.forEach(k=>{
    const arr = state.history.series[k];
    for (let i=i0;i<arr.length;i++) vmax = Math.max(vmax, Math.abs(arr[i]));
  });
  vmax *= 1.15;

  const colors = {};
  let ci = 0; const palette = ['#35d0c0','#eab24d','#e2555a','#9a6fe0','#59c97a','#4a9ce0'];
  keys.forEach(k=> colors[k]=palette[(ci++)%palette.length]);

  keys.forEach(k=>{
    const arr = state.history.series[k];
    scopeCtx.strokeStyle = colors[k]; scopeCtx.lineWidth = 1.6; scopeCtx.beginPath();
    let started = false;
    for (let i=i0;i<arr.length;i++){
      const t = tArr[i];
      const x = ((t-tStart)/SCOPE_WINDOW)*w;
      const y = h/2 - (arr[i]/vmax)*(h/2-8);
      if (!started){ scopeCtx.moveTo(x,y); started=true; } else scopeCtx.lineTo(x,y);
    }
    scopeCtx.stroke();
  });

  document.getElementById('scope-timebase').textContent = (SCOPE_WINDOW*1000).toFixed(0)+' ms window · ±'+vmax.toFixed(2)+' V';
  const legend = document.getElementById('scope-legend');
  legend.innerHTML = keys.slice(0,4).map(k=>{
    const name = k.startsWith('probe:') ? 'Probe' : (circuit.components.find(c=>c.id===k)?.label || COMP[circuit.components.find(c=>c.id===k)?.type]?.label || k);
    return `<span class="chip"><i style="background:${colors[k]}"></i>${name}</span>`;
  }).join('');
}
function drawScopeIdle(w,h){
  scopeCtx.fillStyle = state.theme==='light' ? 'rgba(85,95,114,.6)' : 'rgba(154,164,184,.4)'; scopeCtx.font = '11px var(--mono)';
  scopeCtx.textAlign='center';
  scopeCtx.fillText('Run the simulation or add a probe to see live waveforms', w/2, h/2);
}

function renderMeters(){
  const grid = document.getElementById('meter-grid');
  if (!sim.lastResult){ grid.innerHTML = '<div class="meter-empty">Place probes or run simulation to see readings.</div>'; return; }
  let html = '';
  state.probes.forEach((pr,i)=>{
    const term = circuit.terminalNear(pr.a.x, pr.a.y, 0.5);
    let v = 0;
    if (term){ v = nodeVoltage(sim.lastResult.V, nodeOf(sim.info, term.comp.id, term.idx)); }
    html += `<div class="meter probe"><div class="ml">Probe ${i+1}</div><div class="mv">${fmtEng(v,'V')}</div></div>`;
  });
  circuit.components.forEach(c=>{
    if (c.type==='ammeter'){
      html += `<div class="meter probe"><div class="ml">${c.label||'Ammeter'}</div><div class="mv">${fmtEng(c._i||0,'A')}</div></div>`;
    }
  });
  grid.innerHTML = html || '<div class="meter-empty">Place probes or run simulation to see readings.</div>';
}

document.getElementById('btn-run').addEventListener('click', toggleRun);
document.getElementById('btn-dc').addEventListener('click', ()=>{
  const result = solveDCOperatingPoint(circuit);
  if (!result){ toast('Add a ground symbol before solving.', 'err'); return; }
  sim.lastResult = result;
  log('DC operating point solved', 'ok');
  renderMeters();
  if ([...state.selection].length===1) updatePropReadouts(circuit.components.find(c=>state.selection.has(c.id)));
  toast('DC operating point solved');
});

document.getElementById('sim-speed').addEventListener('change', e=>{
  state.simSpeed = parseFloat(e.target.value) || 1;
  log('Simulation speed set to '+state.simSpeed+'×');
});

/* ============================================================
   11. SAVE / LOAD / EXAMPLES
============================================================ */
function saveCircuit(){
  const blob = new Blob([circuit.toJSON()], {type:'application/json'});
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url; a.download = 'voltra-circuit.json'; a.click();
  URL.revokeObjectURL(url);
  log('Circuit saved to file', 'ok');
}
document.getElementById('btn-save').addEventListener('click', saveCircuit);

document.getElementById('btn-new').addEventListener('click', ()=>{
  if (circuit.components.length && !confirm('Start a new circuit? Unsaved work will be lost.')) return;
  stopSim();
  circuit.clear(); state.selection.clear(); state.wireSelection.clear(); state.probes = [];
  sim.lastResult = null; state.history = {t:[],series:{}};
  renderAll(); updatePropsPanel(); refreshNetlist(); renderMeters();
  log('New circuit');
});

document.getElementById('btn-open').addEventListener('click', ()=> openExamplesModal());
document.getElementById('fileinput').addEventListener('change', e=>{
  const file = e.target.files[0]; if (!file) return;
  const reader = new FileReader();
  reader.onload = ()=>{
    try{
      circuit.fromJSON(reader.result);
      state.selection.clear(); state.wireSelection.clear(); sim.lastResult=null;
      renderAll(); updatePropsPanel(); refreshNetlist();
      log('Circuit loaded from file', 'ok'); toast('Circuit loaded');
    }catch(err){ toast('Could not parse that file', 'err'); log('Load failed: '+err.message, 'err'); }
  };
  reader.readAsText(file);
});

/* ---- example circuits ---- */
const EXAMPLES = {
  'voltage-divider': {
    title:'Voltage Divider', desc:'Two resistors split a 9V supply.',
    build(c){
      c.clear();
      const bat = c.addComponent('battery', -4, -2, 3, {voltage:9});
      const gnd = c.addComponent('ground', -4, 2, 0);
      const r1 = c.addComponent('resistor', 2, -4, 1, {resistance:1000});
      const r2 = c.addComponent('resistor', 2, 0, 1, {resistance:2000});
      // battery top (+) -> across to r1 left
      c.addWire(-4,-4,-4,-6); c.addWire(-4,-6,2,-6); c.addWire(2,-6,2,-5.5);
      // r1 right -> r2 left (node between)
      c.addWire(2,-2.5,2,-1.5);
      // r2 right -> down to ground rail
      c.addWire(2,1.5,2,4); c.addWire(2,4,-4,4); c.addWire(-4,4,-4,1);
      // battery bottom (-) -> ground rail
      c.addWire(-4,-1,-4,0);
    }
  },
  'rc-charging': {
    title:'RC Charging', desc:'Resistor + capacitor transient response.',
    build(c){
      c.clear();
      const bat = c.addComponent('battery', -6, -2, 3, {voltage:5});
      const sw = c.addComponent('switch', -6, -6, 1, {closed:true});
      const r = c.addComponent('resistor', -1, -6, 1, {resistance:1000});
      const cap = c.addComponent('capacitor', 3, -2, 3, {capacitance:1e-6, ic:0});
      const gnd = c.addComponent('ground', -6, 2, 0);
      // battery + -> up to switch
      c.addWire(-6,-4,-6,-6);
      // switch -> resistor
      c.addWire(-4.5,-6,-2.5,-6);
      // resistor -> capacitor top
      c.addWire(0.5,-6,3,-6); c.addWire(3,-6,3,-3.5);
      // ground rail
      c.addWire(-6,4,-6,0); c.addWire(-6,4,3,4); c.addWire(3,4,3,-0.5);
    }
  },
  'led-circuit': {
    title:'LED + Resistor', desc:'Current-limited LED on 9V.',
    build(c){
      c.clear();
      const bat = c.addComponent('battery', -5, -2, 3, {voltage:9});
      const r = c.addComponent('resistor', -1, -5, 1, {resistance:470});
      const led = c.addComponent('led', 3, -2, 3, {vf:2.0, color:'#e2555a'});
      const gnd = c.addComponent('ground', -5, 2, 0);
      c.addWire(-5,-4,-5,-5); c.addWire(-5,-5,-2.5,-5);
      c.addWire(0.5,-5,3,-5); c.addWire(3,-5,3,-3.5);
      c.addWire(3,-0.5,3,4); c.addWire(3,4,-5,4); c.addWire(-5,4,-5,0);
    }
  },
  'rlc-series': {
    title:'Series RLC', desc:'AC source driving R, L and C in series.',
    build(c){
      c.clear();
      const ac = c.addComponent('acsource', -6, -2, 3, {amplitude:5, frequency:60, waveform:'sine'});
      const r = c.addComponent('resistor', -1, -6, 1, {resistance:100});
      const l = c.addComponent('inductor', 3, -6, 1, {inductance:0.05});
      const cap = c.addComponent('capacitor', 6, -2, 3, {capacitance:1e-5});
      const gnd = c.addComponent('ground', -6, 2, 0);
      c.addWire(-6,-4,-6,-6); c.addWire(-6,-6,-2.5,-6);
      c.addWire(0.5,-6,1.5,-6);
      c.addWire(4.5,-6,6,-6); c.addWire(6,-6,6,-3.5);
      c.addWire(6,-0.5,6,4); c.addWire(6,4,-6,4); c.addWire(-6,4,-6,0);
    }
  }
};

function openExamplesModal(){
  const grid = document.getElementById('examples-grid');
  grid.innerHTML = '';
  Object.entries(EXAMPLES).forEach(([key,ex])=>{
    const card = document.createElement('div');
    card.className = 'example-card';
    card.innerHTML = `<div class="et">${ex.title}</div><div class="ed">${ex.desc}</div>`;
    card.addEventListener('click', ()=>{
      stopSim();
      ex.build(circuit);
      state.selection.clear(); state.wireSelection.clear(); sim.lastResult=null;
      state.history={t:[],series:{}}; state.probes=[];
      renderAll(); updatePropsPanel(); refreshNetlist(); renderMeters();
      closeModal();
      log('Loaded example: '+ex.title, 'ok');
      document.getElementById('btn-fit').click();
    });
    grid.appendChild(card);
  });
  document.getElementById('modal-backdrop').style.display = 'flex';
}
function closeModal(){ document.getElementById('modal-backdrop').style.display='none'; }
document.getElementById('modal-close').addEventListener('click', closeModal);
document.getElementById('modal-backdrop').addEventListener('click', e=>{ if (e.target.id==='modal-backdrop') closeModal(); });

/* ============================================================
   VIEW TOGGLE, ZOOM CONTROLS
============================================================ */
document.getElementById('viewrocker').addEventListener('click', ()=>{
  state.view = state.view === 'schematic' ? 'realistic' : 'schematic';
  document.getElementById('viewrocker').classList.toggle('on', state.view==='realistic');
  document.getElementById('lbl-schem').classList.toggle('on', state.view==='schematic');
  document.getElementById('lbl-real').classList.toggle('on', state.view==='realistic');
  buildPalette(document.getElementById('partsearch').value);
  renderAll();
  log('Switched to '+state.view+' view');
});

document.getElementById('btn-zoomin').addEventListener('click', ()=>{ state.zoom=Math.min(4,state.zoom*1.2); renderAll(); });
document.getElementById('btn-zoomout').addEventListener('click', ()=>{ state.zoom=Math.max(0.25,state.zoom/1.2); renderAll(); });
document.getElementById('btn-fit').addEventListener('click', ()=>{
  if (!circuit.components.length){ state.zoom=1; state.pan={x:stageWrap.clientWidth/2, y:stageWrap.clientHeight/2}; renderAll(); return; }
  let minx=Infinity,maxx=-Infinity,miny=Infinity,maxy=-Infinity;
  circuit.components.forEach(c=>{ minx=Math.min(minx,c.x-2); maxx=Math.max(maxx,c.x+2); miny=Math.min(miny,c.y-2); maxy=Math.max(maxy,c.y+2); });
  const w = stageWrap.clientWidth, h = stageWrap.clientHeight;
  const cw = (maxx-minx)*GRID, ch = (maxy-miny)*GRID;
  state.zoom = Math.min(2.5, Math.max(0.3, Math.min(w/cw, h/ch)*0.9));
  state.pan.x = w/2 - ((minx+maxx)/2)*GRID*state.zoom;
  state.pan.y = h/2 - ((miny+maxy)/2)*GRID*state.zoom;
  renderAll();
});

/* ============================================================
   THEME SYNC — called by index.html's inline toggle script via
   window.onThemeChange(theme). Canvas-drawn elements (grid dots,
   wires, component strokes, scope background) don't automatically
   pick up CSS custom-property changes, so we mirror the active
   theme into `state.theme` and force a repaint + palette rebuild.
============================================================ */
window.onThemeChange = function(theme){
  state.theme = (theme === 'light') ? 'light' : 'dark';
  buildPalette(document.getElementById('partsearch') ? document.getElementById('partsearch').value : '');
  renderAll();
  if (state.history && state.history.t && state.history.t.length) renderScope();
  else if (scopeCtx) drawScopeIdle(scopeCanvas.clientWidth, scopeCanvas.clientHeight);
};

/* ============================================================
   12. BOOT
============================================================ */
function boot(){
  // pick up whatever theme index.html's inline script already applied
  // to <html data-theme="..."> before this script ran
  const initialTheme = document.documentElement.getAttribute('data-theme');
  state.theme = initialTheme === 'light' ? 'light' : 'dark';

  // populate the parts palette so components can be dragged out
  buildPalette('');

  // size all four stage canvases + the scope canvas to their containers
  resizeCanvases();
  resizeScope();

  // start with the canvas centered on the origin so newly dropped
  // parts land somewhere visible instead of off in a corner
  state.pan.x = stageWrap.clientWidth / 2;
  state.pan.y = stageWrap.clientHeight / 2;

  // sync the toolbar button highlight with the default tool
  setTool('select');

  // initial paint + side panels
  renderAll();
  refreshNetlist();
  renderMeters();

  // keep everything correctly sized as the window/panels resize
  window.addEventListener('resize', ()=>{ resizeCanvases(); resizeScope(); });

  log('Voltra ready — drag a part onto the grid, or click Open for examples.', 'ok');
}

if (document.readyState === 'loading'){
  document.addEventListener('DOMContentLoaded', boot);
} else {
  boot();
}
