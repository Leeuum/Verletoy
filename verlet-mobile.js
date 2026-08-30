// Touch/stylus build of the Verlet sandbox. The physics is unchanged from
// verlet-clean.js; what differs is everything around it:
//
//   * the canvas fills the viewport instead of being a fixed 960x540 box,
//     so the grid is rebuilt on resize/rotate;
//   * physics runs in CSS pixels and the context is scaled by devicePixelRatio,
//     so strokes stay crisp on a Retina iPad without doubling the sim scale;
//   * input is Pointer Events (finger, Apple Pencil and mouse in one path)
//     with palm rejection, and there is a third "erase" mode because a
//     touchscreen has no right button.

const canvas = document.getElementById("game");
const ctx = canvas.getContext("2d", { alpha: false });

const MAX_PARTICLES = 20000;

const posX = new Float32Array(MAX_PARTICLES);
const posY = new Float32Array(MAX_PARTICLES);
const prevX = new Float32Array(MAX_PARTICLES);
const prevY = new Float32Array(MAX_PARTICLES);
let count = 0;
let recycle = 0;

// Defaults trimmed for tablet-class hardware: fewer, slightly bigger
// particles, and a chunkier stroke/eraser that suits a fingertip.
const settings = {

  gravity: 1500,
  damping: 0.999,
  maxSpeed: 3000,

  walls: true,

  substeps: 3,
  passes: 2,
  response: 0.5,
  wallFriction: 0.98,

  radius: 4,
  maxParticles: 2000,

  emitInterval: 20,
  emitPerBurst: 2,
  spread: 8,
  emitSpeed: 1200,

  lineThickness: 8,
  lineFriction: 0.85,
  lineBounce: 0.1,
  drawSpacing: 4,
  eraserSize: 44,
};

// ------------------------------------------------------------- viewport
//
// W/H are the logical (CSS pixel) simulation bounds. The backing store is
// W*dpr by H*dpr and the context carries the dpr scale, so every physics
// and stroke coordinate below is in plain CSS pixels.

const DPR_CAP = 2;
let W = 960, H = 540, dpr = 1;

let cellSize = 0, cols = 0, rows = 0, cellTotal = 0;
let cellStart = new Int32Array(0);
let cursor = new Int32Array(0);
let occupied = new Int32Array(0);
let occupiedCount = 0;
const sorted = new Int32Array(MAX_PARTICLES);

// `force` is for viewport changes: the cell size can be identical while
// cols/rows have to change, so the usual early-out must be skippable.
function resizeGrid(force) {
  const size = Math.max(1, settings.radius * 2);
  if (!force && size === cellSize) return;
  cellSize = size;
  cols = Math.max(1, Math.ceil(W / cellSize));
  rows = Math.max(1, Math.ceil(H / cellSize));
  cellTotal = cols * rows;
  cellStart = new Int32Array(cellTotal + 1);
  cursor = new Int32Array(cellTotal);
  occupied = new Int32Array(cellTotal);
  segGridDirty = true;
}

function resizeCanvas() {
  const rect = canvas.getBoundingClientRect();
  W = Math.max(240, Math.round(rect.width));
  H = Math.max(240, Math.round(rect.height));
  dpr = Math.min(window.devicePixelRatio || 1, DPR_CAP);

  canvas.width = Math.round(W * dpr);
  canvas.height = Math.round(H * dpr);
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);

  resizeGrid(true);
  makeSprite();

  // Anything left outside the new bounds gets pulled back in, otherwise it
  // sits in a clamped edge cell forever after a rotation.
  const r = settings.radius;
  for (let i = 0; i < count; i++) {
    if (posX[i] > W - r) { posX[i] = W - r; prevX[i] = posX[i]; }
    if (posY[i] > H - r) { posY[i] = H - r; prevY[i] = posY[i]; }
    if (posX[i] < r) { posX[i] = r; prevX[i] = posX[i]; }
    if (posY[i] < r) { posY[i] = r; prevY[i] = posY[i]; }
  }
}

function cellOf(i) {
  let cx = (posX[i] / cellSize) | 0;
  let cy = (posY[i] / cellSize) | 0;
  if (cx < 0) cx = 0; else if (cx >= cols) cx = cols - 1;
  if (cy < 0) cy = 0; else if (cy >= rows) cy = rows - 1;
  return cy * cols + cx;
}

function buildGrid() {
  cellStart.fill(0);

  for (let i = 0; i < count; i++) cellStart[cellOf(i) + 1]++;
  for (let c = 0; c < cellTotal; c++) cellStart[c + 1] += cellStart[c];
  cursor.set(cellStart.subarray(0, cellTotal));
  for (let i = 0; i < count; i++) sorted[cursor[cellOf(i)]++] = i;

  occupiedCount = 0;
  for (let c = 0; c < cellTotal; c++) {
    if (cellStart[c + 1] > cellStart[c]) occupied[occupiedCount++] = c;
  }
}

// --------------------------------------------------------- placed objects
//
// Two kinds, one array, no physics of their own: an emitter is a circle that
// sprays particles along a fixed aim vector, a remover is a square that
// deletes any particle whose centre lands inside it. Neither collides.
// {kind:"emit", x, y, vx, vy}  |  {kind:"kill", x, y, hw, hh}

const objects = [];

// Placed emitters carry their own emission settings and their own clock, so
// two of them can run at different rates. The side panel's EMITTER group is
// only the finger emitter now; these are the defaults a fresh one is born with
// and the mini menu (double-tap in Place mode) edits them per object.
const EMIT_DEF = { interval: 105, burst: 1, spread: 0, speed: 1200 };

const EMIT_R = 26;        // emitter circle radius, also the aim-drag full-throw
const KILL_MIN = 14;      // smallest half-extent a drag can leave behind, per axis

// ---------------------------------------------------------------- strokes

const MAX_SEGMENTS = 8000;
const segAX = new Float32Array(MAX_SEGMENTS);
const segAY = new Float32Array(MAX_SEGMENTS);
const segBX = new Float32Array(MAX_SEGMENTS);
const segBY = new Float32Array(MAX_SEGMENTS);
let segCount = 0;

const strokes = [];

let segCellStart = new Int32Array(0);
let segCursor = new Int32Array(0);
let segItems = new Int32Array(0);
let segGridDirty = true;

function addSegment(ax, ay, bx, by) {
  if (segCount >= MAX_SEGMENTS) return;
  const s = segCount++;
  segAX[s] = ax; segAY[s] = ay;
  segBX[s] = bx; segBY[s] = by;
  segGridDirty = true;
}

function rebuildSegments() {
  segCount = 0;
  for (const pts of strokes) {
    for (let k = 2; k < pts.length; k += 2) {
      addSegment(pts[k - 2], pts[k - 1], pts[k], pts[k + 1]);
    }
  }
  segGridDirty = true;
}

function segPad() {
  return settings.lineThickness * 0.5 + settings.radius;
}

function forEachSegCell(s, fn) {
  const ax = segAX[s], ay = segAY[s];
  const bx = segBX[s], by = segBY[s];
  const ex = bx - ax, ey = by - ay;
  const lenSq = ex * ex + ey * ey;
  const reach = segPad() + cellSize;

  let minX = Math.min(ax, bx) - reach, maxX = Math.max(ax, bx) + reach;
  let minY = Math.min(ay, by) - reach, maxY = Math.max(ay, by) + reach;

  let c0 = (minX / cellSize) | 0, c1 = (maxX / cellSize) | 0;
  let r0 = (minY / cellSize) | 0, r1 = (maxY / cellSize) | 0;
  if (c0 < 0) c0 = 0; if (c1 >= cols) c1 = cols - 1;
  if (r0 < 0) r0 = 0; if (r1 >= rows) r1 = rows - 1;

  const reachSq = reach * reach;

  for (let cy = r0; cy <= r1; cy++) {
    for (let cx = c0; cx <= c1; cx++) {
      const px = (cx + 0.5) * cellSize;
      const py = (cy + 0.5) * cellSize;
      let t = lenSq > 0 ? ((px - ax) * ex + (py - ay) * ey) / lenSq : 0;
      if (t < 0) t = 0; else if (t > 1) t = 1;
      const dx = px - (ax + ex * t);
      const dy = py - (ay + ey * t);
      if (dx * dx + dy * dy <= reachSq) fn(cy * cols + cx);
    }
  }
}

function buildSegGrid() {
  segGridDirty = false;
  if (segCellStart.length !== cellTotal + 1) {
    segCellStart = new Int32Array(cellTotal + 1);
    segCursor = new Int32Array(cellTotal);
  }
  segCellStart.fill(0);
  if (segCount === 0) return;

  let pairs = 0;
  for (let s = 0; s < segCount; s++) {
    forEachSegCell(s, (c) => { segCellStart[c + 1]++; pairs++; });
  }
  for (let c = 0; c < cellTotal; c++) segCellStart[c + 1] += segCellStart[c];

  if (segItems.length < pairs) segItems = new Int32Array(pairs * 2);
  segCursor.set(segCellStart.subarray(0, cellTotal));
  for (let s = 0; s < segCount; s++) {
    forEachSegCell(s, (c) => { segItems[segCursor[c]++] = s; });
  }
}

// ---------------------------------------------------------------- physics

// Velocity is implied by pos - prev, so a big shove-apart from collide() is
// read back here as speed — that is what flings compacted particles across
// the screen. Clamping the implied velocity is the one choke point that
// catches every source of it (particles, lines, walls, spawn).
function integrate(h) {
  const g = settings.gravity * h * h;
  const d = settings.damping;
  const maxLen = settings.maxSpeed * h;
  const maxSq = maxLen * maxLen;
  for (let i = 0; i < count; i++) {
    let vx = (posX[i] - prevX[i]) * d;
    let vy = (posY[i] - prevY[i]) * d;
    const sq = vx * vx + vy * vy;
    if (sq > maxSq) {
      const s = maxLen / Math.sqrt(sq);
      vx *= s; vy *= s;
    }
    prevX[i] = posX[i];
    prevY[i] = posY[i];
    posX[i] += vx;
    posY[i] += vy + g;
  }
}

function collide() {
  const diameter = cellSize;
  const dSq = diameter * diameter;
  const resp = settings.response * 0.5;

  for (let o = 0; o < occupiedCount; o++) {
    const c = occupied[o];
    const cx = c % cols;
    const cy = (c / cols) | 0;
    const aStart = cellStart[c], aEnd = cellStart[c + 1];
    const hasRight = cx < cols - 1;
    const hasBelow = cy < rows - 1;

    for (let a = aStart; a < aEnd; a++) {
      const i = sorted[a];

      let ix = posX[i], iy = posY[i];

      for (let k = 0; k < 5; k++) {
        let bStart, bEnd;
        if (k === 0) {
          bStart = a + 1; bEnd = aEnd;
        } else if (k === 1) {
          if (!hasRight) continue;
          bStart = cellStart[c + 1]; bEnd = cellStart[c + 2];
        } else {
          if (!hasBelow) continue;
          const nx = cx + (k - 3);
          if (nx < 0 || nx >= cols) continue;
          const n = c + cols + (k - 3);
          bStart = cellStart[n]; bEnd = cellStart[n + 1];
        }

        for (let b = bStart; b < bEnd; b++) {
          const j = sorted[b];
          const dx = posX[j] - ix;
          const dy = posY[j] - iy;
          const distSq = dx * dx + dy * dy;

          if (distSq >= dSq || distSq === 0) continue;

          const dist = Math.sqrt(distSq);
          const push = ((diameter - dist) / dist) * resp;
          const ox = dx * push, oy = dy * push;
          ix -= ox; iy -= oy;
          posX[j] += ox; posY[j] += oy;
        }
      }

      posX[i] = ix; posY[i] = iy;
    }
  }
}

function collideLines() {
  if (segCount === 0) return;

  const minDist = segPad();
  const minSq = minDist * minDist;
  const fric = settings.lineFriction;
  const bounce = settings.lineBounce;

  for (let i = 0; i < count; i++) {
    let cx = (posX[i] / cellSize) | 0;
    let cy = (posY[i] / cellSize) | 0;
    if (cx < 0) cx = 0; else if (cx >= cols) cx = cols - 1;
    if (cy < 0) cy = 0; else if (cy >= rows) cy = rows - 1;

    const c = cy * cols + cx;
    const start = segCellStart[c], end = segCellStart[c + 1];
    if (start === end) continue;

    let px = posX[i], py = posY[i];
    const opx = prevX[i], opy = prevY[i];

    for (let k = start; k < end; k++) {
      const s = segItems[k];
      const ax = segAX[s], ay = segAY[s];
      const ex = segBX[s] - ax, ey = segBY[s] - ay;
      const lenSq = ex * ex + ey * ey;

      let nx = 0, ny = 0, hit = false;
      let hx = px, hy = py;

      if (lenSq > 1e-9) {
        const l = Math.sqrt(lenSq);
        const lnx = -ey / l, lny = ex / l;
        const sPos = (px - ax) * lnx + (py - ay) * lny;
        const sPrev = (opx - ax) * lnx + (opy - ay) * lny;
        if (sPos * sPrev < 0) {
          const u = sPrev / (sPrev - sPos);
          const cxp = opx + (px - opx) * u;
          const cyp = opy + (py - opy) * u;
          const t = ((cxp - ax) * ex + (cyp - ay) * ey) / lenSq;
          if (t > -0.15 && t < 1.15) {
            const sgn = sPrev > 0 ? 1 : -1;
            nx = lnx * sgn; ny = lny * sgn;
            hx = cxp; hy = cyp;
            hit = true;
          }
        }
      }

      if (!hit) {
        let t = lenSq > 0 ? ((px - ax) * ex + (py - ay) * ey) / lenSq : 0;
        if (t < 0) t = 0; else if (t > 1) t = 1;
        const qx = ax + ex * t, qy = ay + ey * t;
        const dx = px - qx, dy = py - qy;
        const distSq = dx * dx + dy * dy;
        if (distSq >= minSq) continue;

        hx = qx; hy = qy;
        const dist = Math.sqrt(distSq);
        if (dist > 1e-6) {
          nx = dx / dist; ny = dy / dist;
        } else {
          const l = Math.sqrt(lenSq) || 1;
          nx = -ey / l; ny = ex / l;
          if ((opx - qx) * nx + (opy - qy) * ny < 0) { nx = -nx; ny = -ny; }
        }
      }

      const vx = px - prevX[i], vy = py - prevY[i];

      px = hx + nx * minDist;
      py = hy + ny * minDist;

      const vn = vx * nx + vy * ny;
      const vtx = vx - vn * nx, vty = vy - vn * ny;
      const rn = vn < 0 ? -vn * bounce : vn;
      prevX[i] = px - (vtx * fric + nx * rn);
      prevY[i] = py - (vty * fric + ny * rn);
    }

    posX[i] = px;
    posY[i] = py;
  }
}

function constrainWalls() {
  const r = settings.radius;
  const f = settings.wallFriction;
  const maxX = W - r;
  const maxY = H - r;

  // Edges off: the viewport border acts like a remover. Particles are only
  // dropped once fully outside, so they fly off screen instead of popping at
  // the rim. Same swap-delete as applyRemovers(). Skipped during a benchmark,
  // which owns `count` itself.
  if (!settings.walls && !bench.on) {
    for (let i = count - 1; i >= 0; i--) {
      if (posX[i] > -r && posX[i] < W + r && posY[i] > -r && posY[i] < H + r) continue;
      const last = --count;
      posX[i] = posX[last]; posY[i] = posY[last];
      prevX[i] = prevX[last]; prevY[i] = prevY[last];
    }
    if (recycle > count) recycle = 0;
    return;
  }

  for (let i = 0; i < count; i++) {
    if (posX[i] < r) {
      posX[i] = r;
      prevY[i] = posY[i] - (posY[i] - prevY[i]) * f;
    } else if (posX[i] > maxX) {
      posX[i] = maxX;
      prevY[i] = posY[i] - (posY[i] - prevY[i]) * f;
    }
    if (posY[i] < r) {
      posY[i] = r;
      prevX[i] = posX[i] - (posX[i] - prevX[i]) * f;
    } else if (posY[i] > maxY) {
      posY[i] = maxY;
      prevX[i] = posX[i] - (posX[i] - prevX[i]) * f;
    }
  }
}

function step(seconds) {
  if (segGridDirty) buildSegGrid();

  const h = seconds / settings.substeps;
  for (let s = 0; s < settings.substeps; s++) {
    integrate(h);
    buildGrid();
    for (let p = 0; p < settings.passes; p++) {
      collide();
      collideLines();
    }
    constrainWalls();
  }
  if (objects.length && !bench.on) applyRemovers();
}

// ------------------------------------------------------------------ input

let emitting = false;
let emitTimer = 0;
const point = { x: 0, y: 0 };

// The canvas CSS box and the logical sim size are the same thing here, but
// the ratio is kept in case a browser rounds the box to a fractional size.
function trackPointer(e) {
  const rect = canvas.getBoundingClientRect();
  point.x = (e.clientX - rect.left) * (W / rect.width);
  point.y = (e.clientY - rect.top) * (H / rect.height);
}

function spawn(x, y, vx = 0, vy = 0, spread = settings.spread) {
  const limit = settings.maxParticles;
  let i;
  if (count < limit) {
    i = count++;
  } else {
    i = recycle;
    recycle = recycle + 1 >= limit ? 0 : recycle + 1;
  }

  const s = spread;
  posX[i] = x + (Math.random() - 0.5) * s;
  posY[i] = y + (Math.random() - 0.5) * s;

  // Velocity is implied by pos - prev, so a launch speed is set by placing
  // prev one substep's worth of travel behind the spawn point.
  const h = vx || vy ? STEP / 1000 / settings.substeps : 0;
  prevX[i] = posX[i] - vx * h;
  prevY[i] = posY[i] - vy * h;
}

// Removers, applied once per fixed step: swap the dead particle with the last
// live one and shrink `count`. Order is meaningless here, so the swap is free.
function applyRemovers() {
  for (const o of objects) {
    if (o.kind !== "kill") continue;
    for (let i = count - 1; i >= 0; i--) {
      if (Math.abs(posX[i] - o.x) > o.hw || Math.abs(posY[i] - o.y) > o.hh) continue;
      const last = --count;
      posX[i] = posX[last]; posY[i] = posY[last];
      prevX[i] = prevX[last]; prevY[i] = prevY[last];
    }
  }
  if (recycle > count) recycle = 0;
}

let mode = "emit";
let currentStroke = null;
let placeKind = "emit";   // which object the Place button drops
let placing = null;       // the object being dragged out right now
let placingIsNew = false; // false when the drag is re-shaping an existing one

function setMode(next) {
  // Tapping Place while already in it flips between emitter and remover.
  if (next === "place" && mode === "place") {
    placeKind = placeKind === "emit" ? "kill" : "emit";
  }
  mode = next;
  closeMini();
  stopInput();
  canvas.style.cursor = next === "emit" ? "default" : "crosshair";
  updateModeButtons();
}

// Press drops the object, the drag shapes it: for an emitter the drag is the
// aim handle (direction, and distance-to-rim as a fraction of launch speed),
// for a remover it is the rectangle's half-width and half-height, sized
// independently so the box can be any aspect.
function startPlace(x, y) {
  // Press on an object already there and the drag re-shapes that one (re-aim
  // an emitter, resize a remover) instead of dropping a new one on top.
  for (let i = objects.length - 1; i >= 0; i--) {
    if (objectHit(objects[i], x, y, 0)) {
      placing = objects[i];
      placingIsNew = false;
      return;
    }
  }
  placing = placeKind === "emit"
    ? { kind: "emit", x, y, vx: 0, vy: 0, t: 0, ...EMIT_DEF }
    : { kind: "kill", x, y, hw: KILL_MIN, hh: KILL_MIN };
  placingIsNew = true;
  objects.push(placing);
}

function dragPlace(x, y) {
  const dx = x - placing.x, dy = y - placing.y;
  if (placing.kind === "kill") {
    placing.hw = Math.max(KILL_MIN, Math.abs(dx));
    placing.hh = Math.max(KILL_MIN, Math.abs(dy));
    return;
  }
  const d = Math.hypot(dx, dy);
  if (d < 1) { placing.vx = placing.vy = 0; return; }
  const speed = Math.min(d / EMIT_R, 1) * placing.speed;
  placing.vx = (dx / d) * speed;
  placing.vy = (dy / d) * speed;
  if (placing === miniObj) positionMini();
}

function objectHit(o, x, y, pad) {
  const rx = (o.kind === "emit" ? EMIT_R : o.hw) + pad;
  const ry = (o.kind === "emit" ? EMIT_R : o.hh) + pad;
  return Math.abs(x - o.x) <= rx && Math.abs(y - o.y) <= ry;
}

function emitterAt(x, y) {
  for (let i = objects.length - 1; i >= 0; i--) {
    const o = objects[i];
    if (o.kind === "emit" && objectHit(o, x, y, 0)) return o;
  }
  return null;
}

function startStroke(x, y) {
  currentStroke = [x, y];
  strokes.push(currentStroke);
}

function extendStroke(x, y) {
  const n = currentStroke.length;
  const dx = x - currentStroke[n - 2];
  const dy = y - currentStroke[n - 1];
  const spacing = settings.drawSpacing;
  if (dx * dx + dy * dy < spacing * spacing) return;
  currentStroke.push(x, y);
  addSegment(currentStroke[n - 2], currentStroke[n - 1], x, y);
}

function eraseAt(x, y) {
  const r = settings.eraserSize * 0.5;
  const rSq = r * r;
  let removed = false;

  for (let i = objects.length - 1; i >= 0; i--) {
    if (objectHit(objects[i], x, y, r)) {
      if (objects[i] === miniObj) closeMini();
      objects.splice(i, 1);
    }
  }

  for (let s = strokes.length - 1; s >= 0; s--) {
    const pts = strokes[s];
    for (let k = 0; k < pts.length; k += 2) {
      const dx = pts[k] - x, dy = pts[k + 1] - y;
      if (dx * dx + dy * dy <= rSq) {
        strokes.splice(s, 1);
        removed = true;
        break;
      }
    }
  }

  if (removed) rebuildSegments();
}

// ------------------------------------------------------- pointer plumbing
//
// One gesture at a time. `active` remembers which pointer owns it so extra
// fingers (and a palm resting on the glass) are ignored rather than fighting
// the one that started the stroke.

const active = { id: null, type: null, action: null };
let lastTap = { t: -1e9, x: 0, y: 0 };
let lastPenAt = -1e9;
const PALM_GRACE = 700;   // ms after a pen event during which touches are ignored
const DOUBLE_TAP = 350;   // ms window for a double-tap, on the canvas or a toolbar button

function penRecentlyUsed() {
  return performance.now() - lastPenAt < PALM_GRACE;
}

// Apple Pencil Pro / any stylus flipped to its eraser end reports button 5,
// or bit 5 (32) in `buttons`. Treat that as erase whatever the current mode.
function isEraserTip(e) {
  return e.pointerType === "pen" && (e.button === 5 || (e.buttons & 32) !== 0);
}

function beginAction(action) {
  active.action = action;

  if (action === "emit") {
    emitting = true;
    emitTimer = 0;
    for (let n = 0; n < settings.emitPerBurst; n++) spawn(point.x, point.y);
  } else if (action === "draw") {
    startStroke(point.x, point.y);
  } else if (action === "place") {
    startPlace(point.x, point.y);
  } else {
    eraseAt(point.x, point.y);
  }
}

// A palm that lands *before* the pen would otherwise own the gesture, so a
// pen arriving mid-gesture takes over and throws away what the palm did.
function abortAction() {
  if (active.action === "draw" && currentStroke) {
    const i = strokes.indexOf(currentStroke);
    if (i !== -1) strokes.splice(i, 1);
    rebuildSegments();
  }
  if (active.action === "place" && placing && placingIsNew) {
    const i = objects.indexOf(placing);
    if (i !== -1) objects.splice(i, 1);
  }
  stopInput();
}

canvas.addEventListener("pointerdown", (e) => {
  if (bench.on) return;
  if (e.pointerType === "pen") lastPenAt = performance.now();

  if (active.id !== null) {
    if (e.pointerType === "pen" && active.type !== "pen") abortAction();
    else return;
  }

  // Fingers are ignored while the Pencil is (or has just been) in play.
  if (e.pointerType === "touch" && penRecentlyUsed()) return;
  // Mouse: only the left button starts anything; right-drag still erases.
  if (e.pointerType === "mouse" && e.button !== 0 && e.button !== 2) return;

  e.preventDefault();
  trackPointer(e);

  // Double-tap an emitter in Place mode opens its mini menu; the first tap
  // has already come and gone as a zero-length re-aim, which changes nothing.
  const tapped = mode === "place" ? emitterAt(point.x, point.y) : null;
  const doubled = tapped && performance.now() - lastTap.t < DOUBLE_TAP &&
                  Math.hypot(point.x - lastTap.x, point.y - lastTap.y) < 24;
  lastTap = { t: performance.now(), x: point.x, y: point.y };
  if (doubled) { tapped === miniObj ? closeMini() : openMini(tapped); return; }

  active.id = e.pointerId;
  active.type = e.pointerType;
  canvas.setPointerCapture(e.pointerId);

  const rightClick = e.pointerType === "mouse" && e.button === 2;
  beginAction(isEraserTip(e) || rightClick ? "erase" : mode);
});

canvas.addEventListener("pointermove", (e) => {
  if (e.pointerType === "pen") lastPenAt = performance.now();
  if (e.pointerId !== active.id) return;

  e.preventDefault();

  // Coalesced events give the Pencil's full ~240Hz sample stream, so fast
  // strokes come out smooth instead of as a chain of long straight chords.
  const events = e.getCoalescedEvents ? e.getCoalescedEvents() : [e];
  for (const ev of (events.length ? events : [e])) {
    trackPointer(ev);
    if (active.action === "draw" && currentStroke) extendStroke(point.x, point.y);
    else if (active.action === "place" && placing) dragPlace(point.x, point.y);
    else if (active.action === "erase") eraseAt(point.x, point.y);
  }
  trackPointer(e);
});

function stopInput() {
  emitting = false;
  currentStroke = null;
  placing = null;
  active.id = null;
  active.type = null;
  active.action = null;
}

function endPointer(e) {
  if (e.pointerId !== active.id) return;
  if (canvas.hasPointerCapture(e.pointerId)) canvas.releasePointerCapture(e.pointerId);
  stopInput();
}

canvas.addEventListener("pointerup", endPointer);
canvas.addEventListener("pointercancel", endPointer);
window.addEventListener("blur", stopInput);

// Belt and braces against iOS gestures that touch-action alone doesn't cover.
// Note: deliberately no preventDefault on touchstart — in WebKit that can
// cancel the pointer stream mid-gesture, which is exactly what kills drawing.
canvas.addEventListener("contextmenu", (e) => e.preventDefault());
canvas.addEventListener("dblclick", (e) => e.preventDefault());
document.addEventListener("gesturestart", (e) => e.preventDefault());
document.addEventListener("gesturechange", (e) => e.preventDefault());

window.addEventListener("keydown", (e) => {
  if (e.target instanceof HTMLInputElement) return;
  const k = e.key.toLowerCase();
  if (k === "e") setMode("emit");
  else if (k === "d") setMode("draw");
  else if (k === "x") setMode("erase");
  else if (k === "p") setMode("place");
});

// -------------------------------------------------------------- rendering

// Canvas colours live in the same :root theme block as the CSS (index.html),
// so a retheme is one paste rather than two. Read once at load — they are not
// meant to change at runtime.
const COL = (() => {
  const cs = getComputedStyle(document.documentElement);
  const g = (k, fallback) => cs.getPropertyValue(k).trim() || fallback;
  return {
    canvas:   g("--canvas-bg", "#1c1c1c"),
    particle: g("--particle", "#ffffff"),
    stroke:   g("--stroke-col", "#8899aa"),
    eraser:   g("--eraser", "#ff6666"),
    emitter:  g("--emitter", "#66ff99"),
    remover:  g("--remover", "#ff6e6e"),
  };
})();

let sprite = null;
let spriteSize = 0;
let spriteHalf = 0;

// The sprite is rasterised at device resolution but drawn at its logical
// size, so particles stay round rather than fuzzy on a Retina screen.
function makeSprite() {
  const r = settings.radius;
  spriteSize = Math.ceil(r * 2) + 2;
  const px = Math.ceil(spriteSize * dpr);

  sprite = document.createElement("canvas");
  sprite.width = sprite.height = px;
  const sctx = sprite.getContext("2d");
  sctx.scale(px / spriteSize, px / spriteSize);
  sctx.fillStyle = COL.particle;
  sctx.beginPath();
  sctx.arc(spriteSize / 2, spriteSize / 2, r, 0, Math.PI * 2);
  sctx.fill();

  spriteHalf = spriteSize / 2;
}

function drawStrokes() {
  if (strokes.length === 0) return;

  ctx.strokeStyle = COL.stroke;
  ctx.fillStyle = COL.stroke;
  ctx.lineWidth = settings.lineThickness;
  ctx.lineCap = "round";
  ctx.lineJoin = "round";

  for (const pts of strokes) {
    if (pts.length < 4) {
      ctx.beginPath();
      ctx.arc(pts[0], pts[1], settings.lineThickness * 0.5, 0, Math.PI * 2);
      ctx.fill();
      continue;
    }
    ctx.beginPath();
    ctx.moveTo(pts[0], pts[1]);
    for (let k = 2; k < pts.length; k += 2) ctx.lineTo(pts[k], pts[k + 1]);
    ctx.stroke();
  }
}

// Emitter: a ring with the aim dot pushed out from the centre in the launch
// direction, so the angle and the throttle are both readable at a glance.
// Remover: a red rectangle. Both are drawn under the particles.
function drawObjects() {
  for (const o of objects) {
    if (o.kind === "kill") {
      ctx.strokeStyle = COL.remover;
      ctx.lineWidth = 2;
      ctx.strokeRect(o.x - o.hw, o.y - o.hh, o.hw * 2, o.hh * 2);
      continue;
    }
    ctx.strokeStyle = COL.emitter;
    ctx.fillStyle = COL.emitter;
    ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.arc(o.x, o.y, EMIT_R, 0, Math.PI * 2);
    ctx.stroke();

    const speed = Math.hypot(o.vx, o.vy);
    const t = speed > 0 ? Math.min(speed / o.speed, 1) : 0;
    ctx.beginPath();
    ctx.arc(o.x + (o.vx / (speed || 1)) * EMIT_R * t * 0.72,
            o.y + (o.vy / (speed || 1)) * EMIT_R * t * 0.72,
            3.5, 0, Math.PI * 2);
    ctx.fill();
  }
}

// In erase mode the brush is invisible on a touchscreen — there is no cursor
// — so the last known point gets a ring the size of the eraser.
function drawEraserRing() {
  if (mode !== "erase" && active.action !== "erase") return;
  ctx.strokeStyle = COL.eraser;
  ctx.lineWidth = 1.5;
  ctx.beginPath();
  ctx.arc(point.x, point.y, settings.eraserSize * 0.5, 0, Math.PI * 2);
  ctx.stroke();
}

function draw() {
  ctx.fillStyle = COL.canvas;
  ctx.fillRect(0, 0, W, H);
  drawStrokes();
  drawObjects();
  for (let i = 0; i < count; i++) {
    ctx.drawImage(sprite, posX[i] - spriteHalf, posY[i] - spriteHalf, spriteSize, spriteSize);
  }
  drawEraserRing();
}

// -------------------------------------------------- emitter mini menu
//
// Double-tap an emitter in Place mode to edit that one emitter without going
// near the side panel. Same .row markup as the panel, so the sliders inherit
// its fat touch targets. Opens on the side away from the emission, right if
// there is no aim yet, and is clamped to stay on screen.

const mini = document.getElementById("mini");
let miniObj = null;

const MINI_ROWS = [
  // Rate reads the interval backwards, so dragging right emits faster.
  { label: "Rate", min: 5, max: 300, step: 5,
    get: (o) => 305 - o.interval, set: (o, v) => { o.interval = 305 - v; } },
  { label: "Particles", min: 1, max: 40, step: 1,
    get: (o) => o.burst, set: (o, v) => { o.burst = v; } },
  { label: "Scatter", min: 0, max: 60, step: 1,
    get: (o) => o.spread, set: (o, v) => { o.spread = v; } },
  // Speed rescales the aim vector the drag produced, keeping its direction —
  // and becomes the emitter's new full-throw, so a later re-aim matches it.
  // Floored above zero because a zero vector has no direction left to restore.
  { label: "Speed", min: 50, max: 4000, step: 50,
    get: (o) => Math.round(Math.hypot(o.vx, o.vy)) || o.speed,
    set: (o, v) => {
      const d = Math.hypot(o.vx, o.vy);
      o.speed = v;
      if (d) { o.vx = (o.vx / d) * v; o.vy = (o.vy / d) * v; }
    } },
];

// Label flanked by \u2212/+ steppers, slider underneath. Shared by the emitter
// menu and the toolbar panels; the caller supplies where the value goes.
function sliderRow(parent, spec) {
  const row = document.createElement("div");
  row.className = "row";

  const lab = document.createElement("div");
  lab.className = "lab";
  const minus = document.createElement("button");
  minus.textContent = "\u2212";
  const plus = document.createElement("button");
  plus.textContent = "+";
  const name = document.createElement("label");
  name.textContent = spec.label;
  lab.append(minus, name, plus);

  const inputs = document.createElement("div");
  inputs.className = "inputs";
  const range = document.createElement("input");
  range.type = "range";
  range.min = spec.min;
  range.max = spec.max;
  range.step = spec.step;
  inputs.append(range);

  const apply = (v) => {
    range.value = Math.min(spec.max, Math.max(spec.min, v));
    spec.set(+range.value);
  };
  range.addEventListener("input", () => spec.set(+range.value));
  minus.addEventListener("click", () => apply(+range.value - spec.step));
  plus.addEventListener("click", () => apply(+range.value + spec.step));

  row.append(lab, inputs);
  parent.append(row);
  return range;
}

const miniInputs = MINI_ROWS.map((r) =>
  sliderRow(mini, { ...r, set: (v) => { if (miniObj) r.set(miniObj, v); } }));

function openMini(o) {
  miniObj = o;
  MINI_ROWS.forEach((r, i) => { miniInputs[i].value = r.get(o); });
  mini.hidden = false;
  positionMini();
}

function closeMini() {
  miniObj = null;
  mini.hidden = true;
}

function positionMini() {
  const rect = canvas.getBoundingClientRect();
  const w = mini.offsetWidth, h = mini.offsetHeight;
  const gap = EMIT_R + 14;
  const x = miniObj.vx > 0 ? miniObj.x - gap - w : miniObj.x + gap;
  const y = miniObj.y - h / 2;
  mini.style.left = Math.min(Math.max(rect.left + x, 4), innerWidth - w - 4) + "px";
  mini.style.top = Math.min(Math.max(rect.top + y, 4), innerHeight - h - 4) + "px";
}

// ------------------------------------------------------------------ panel

const CONTROLS = [
  { group: "World" },
  { key: "gravity", label: "Gravity (px/s²)", min: -2000, max: 5000, step: 50 },
  { key: "damping", label: "Damping (air drag)", min: 0.9, max: 1, step: 0.001 },
  { key: "maxSpeed", label: "Speed limit (px/s)", min: 500, max: 10000, step: 100 },
  { key: "walls", label: "Canvas collisions", toggle: true },

  { group: "Solver" },
  { key: "substeps", label: "Substeps per frame", min: 1, max: 12, step: 1 },
  { key: "passes", label: "Relaxation passes", min: 1, max: 8, step: 1 },
  { key: "response", label: "Collision stiffness", min: 0.05, max: 1, step: 0.01 },
  { key: "wallFriction", label: "Wall friction", min: 0.5, max: 1, step: 0.005 },

  { group: "Particles" },
  { key: "radius", label: "Radius — rebuilds grid", min: 1, max: 12, step: 0.5 },
  { key: "maxParticles", label: "Max particles — recycles oldest", min: 100, max: MAX_PARTICLES, step: 100 },

];

const panel = document.getElementById("panel");
const panelBody = document.getElementById("panel-body");
const countEl = document.getElementById("count");
const fpsEl = document.getElementById("fps");

function onSettingChanged() {
  resizeGrid();
  makeSprite();
  segGridDirty = true;

  if (count > settings.maxParticles) count = settings.maxParticles;
  if (recycle >= settings.maxParticles) recycle = 0;
}

const modeButtons = {
  emit: document.getElementById("m-emit"),
  draw: document.getElementById("m-draw"),
  erase: document.getElementById("m-erase"),
  place: document.getElementById("m-place"),
};

function updateModeButtons() {
  for (const key in modeButtons) {
    modeButtons[key].classList.toggle("active", key === mode);
  }
  modeButtons.place.textContent =
    placeKind === "emit" ? "Place: Emitter" : "Place: Remover";
}

function decimalsFor(step) {
  const s = String(step);
  return s.includes(".") ? s.split(".")[1].length : 0;
}

// Slider + number pair per key, so the benchmark can write a value back into
// the panel instead of silently changing a setting the UI still shows stale.
const inputsByKey = {};

function setSetting(key, value) {
  settings[key] = value;
  for (const el of inputsByKey[key] || []) el.value = value;
  onSettingChanged();
}

for (const control of CONTROLS) {
  if (control.group) {
    const heading = document.createElement("div");
    heading.className = "group";
    heading.textContent = control.group;
    panelBody.append(heading);
    continue;
  }

  const row = document.createElement("div");
  row.className = "row";
  const label = document.createElement("label");
  label.textContent = control.label;
  const inputs = document.createElement("div");
  inputs.className = "inputs";
  row.append(label, inputs);
  panelBody.append(row);

  if (control.toggle) {
    row.className = "row toggle";
    const box = document.createElement("input");
    box.type = "checkbox";
    box.checked = settings[control.key];
    box.addEventListener("input", () => {
      settings[control.key] = box.checked;
      onSettingChanged();
    });
    inputs.append(box);
    inputsByKey[control.key] = [];
    continue;
  }

  const slider = document.createElement("input");
  slider.type = "range";
  const number = document.createElement("input");
  number.type = "number";
  number.inputMode = "decimal";
  for (const el of [slider, number]) {
    el.min = control.min;
    el.max = control.max;
    el.step = control.step;
    el.value = settings[control.key].toFixed(decimalsFor(control.step));
    el.addEventListener("input", () => {
      const value = Number(el.value);
      if (!Number.isFinite(value)) return;
      settings[control.key] = value;
      const other = el === slider ? number : slider;
      other.value = el.value;
      onSettingChanged();
    });
  }
  inputs.append(slider, number);
  inputsByKey[control.key] = [slider, number];
}

// ------------------------------------------- toolbar mini panels
//
// Double-tap a mode button to hang that mode's settings above the toolbar, so
// the side panel keeps only world/solver/particles. Same .mini shell as the
// emitter menu, one open at a time, and closed whenever the toolbar or the
// viewport moves under it.

const TOOL_PANELS = {
  emit: [
    { key: "emitInterval", label: "Rate", min: 5, max: 300, step: 5 },
    { key: "emitPerBurst", label: "Particles", min: 1, max: 40, step: 1 },
    { key: "spread", label: "Scatter", min: 0, max: 60, step: 1 },
  ],
  draw: [
    { key: "lineThickness", label: "Thickness", min: 1, max: 40, step: 1 },
    { key: "lineFriction", label: "Friction", min: 0, max: 1, step: 0.01 },
    { key: "lineBounce", label: "Bounciness", min: 0, max: 1, step: 0.01 },
    { key: "drawSpacing", label: "Detail", min: 2, max: 30, step: 1 },
  ],
  erase: [
    { key: "eraserSize", label: "Eraser size (px)", min: 8, max: 160, step: 2 },
  ],
};

const toolPanels = {};
let openTool = null;

for (const key in TOOL_PANELS) {
  const el = document.createElement("div");
  el.className = "mini tool";
  el.hidden = true;

  for (const c of TOOL_PANELS[key]) {
    const range = sliderRow(el, { ...c, set: (v) => setSetting(c.key, v) });
    range.value = settings[c.key];
    (inputsByKey[c.key] ||= []).push(range);
  }

  document.body.append(el);
  toolPanels[key] = el;
}

function closeTool() {
  if (openTool) openTool.hidden = true;
  openTool = null;
}

function toggleTool(key) {
  const el = toolPanels[key];
  const wasOpen = openTool === el;
  closeTool();
  if (!el || wasOpen) return;

  el.hidden = false;
  openTool = el;

  // Above its own button, dropping below when the toolbar sits near the top.
  const r = modeButtons[key].getBoundingClientRect();
  const w = el.offsetWidth, h = el.offsetHeight, gap = 8;
  const top = r.top - h - gap < 4 ? r.bottom + gap : r.top - h - gap;
  el.style.left = Math.min(Math.max(r.left, 4), innerWidth - w - 4) + "px";
  el.style.top = Math.min(top, innerHeight - h - 4) + "px";
}

// Second tap on the same button within DOUBLE_TAP opens its panel instead of
// re-running setMode (which would flip Place's kind back).
let lastModeTap = "", lastModeTapAt = 0;

for (const key in modeButtons) {
  modeButtons[key].addEventListener("click", () => {
    const now = performance.now();
    if (lastModeTap === key && now - lastModeTapAt < DOUBLE_TAP) {
      lastModeTap = "";
      toggleTool(key);
      return;
    }
    lastModeTap = key;
    lastModeTapAt = now;
    setMode(key);
  });
}

document.getElementById("clear").addEventListener("click", () => {
  count = 0;
  recycle = 0;
});
document.getElementById("clear-all").addEventListener("click", () => {
  count = 0;
  recycle = 0;
  strokes.length = 0;
  objects.length = 0;
  closeMini();
  rebuildSegments();
});
document.getElementById("gear").addEventListener("click", () => {
  panel.classList.toggle("open");
  stopInput();
});
document.getElementById("close").addEventListener("click", () => {
  panel.classList.remove("open");
});

// Drag the toolbar anywhere. Switching to left/top pins it where it is dropped;
// the CSS centring transform has to go with it.
const bar = document.getElementById("bar");
document.getElementById("grip").addEventListener("pointerdown", (e) => {
  const r = bar.getBoundingClientRect();
  const dx = e.clientX - r.left;
  const dy = e.clientY - r.top;
  e.target.setPointerCapture(e.pointerId);
  closeTool();
  const move = (ev) => {
    const x = Math.min(Math.max(ev.clientX - dx, 0), innerWidth - r.width);
    const y = Math.min(Math.max(ev.clientY - dy, 0), innerHeight - r.height);
    bar.style.cssText = `left:${x}px;top:${y}px;bottom:auto;transform:none`;
  };
  const up = () => {
    e.target.removeEventListener("pointermove", move);
    e.target.removeEventListener("pointerup", up);
    e.target.removeEventListener("pointercancel", up);
  };
  e.target.addEventListener("pointermove", move);
  e.target.addEventListener("pointerup", up);
  e.target.addEventListener("pointercancel", up);
});

const resetButton = document.createElement("button");
resetButton.className = "wide";
resetButton.textContent = "Reset — clear all particles";
resetButton.addEventListener("click", () => { count = 0; recycle = 0; });
panelBody.append(resetButton);

const clearLinesButton = document.createElement("button");
clearLinesButton.className = "wide";
clearLinesButton.textContent = "Clear all drawn lines";
clearLinesButton.addEventListener("click", () => {
  strokes.length = 0;
  rebuildSegments();
});
panelBody.append(clearLinesButton);

// -------------------------------------------------------------- benchmark
//
// Answers one question: how many particles does this machine carry at 60fps,
// at whatever solver quality is currently set.
//
// It does not read the fps counter. rAF is vsync-locked, so fps is quantised
// into 60/30/20 steps — a cliff, not a gradient, and useless to search on.
// What gets timed instead is the wall-clock cost of one 60Hz frame's work:
// median step() plus median draw(). Those are separate numbers on purpose;
// at high counts the per-particle drawImage can outweigh the physics, and
// the fix differs (radius/count vs substeps/passes).
//
// The target is BENCH_BUDGET of the 16.7ms frame, not all of it. A cap tuned
// to sit exactly on the edge falls over the moment the browser does anything
// else. The test scene is a solid packed pile because that is the expensive
// case — loose particles in open space have almost no neighbours to check,
// and a cap tuned on a spray collapses the first time everything lands in
// a heap.
//
// Solver settings are deliberately not searched. Substeps and passes trade
// look for speed, and a script maximising particle count would always drive
// them to 1 and hand back mush. You pick the quality; this finds the count.

const BENCH_BUDGET = 12;      // ms of the 16.7ms frame allowed for physics + draw
const BENCH_SETTLE = 400;     // ms of settling before timing starts
const BENCH_MEASURE = 900;    // ms of timed samples per particle count
const BENCH_TRIES = 6;
const BENCH_LABEL = "Benchmark this machine";
const BENCH_KEY = "verlet-bench";

const bench = {
  on: false,
  phase: "",
  since: 0,
  n: 0,
  tried: [],
  steps: [],
  draws: [],
  capBefore: 0,
};

function median(values) {
  if (!values.length) return 0;
  const sorted = Float64Array.from(values).sort();
  return sorted[sorted.length >> 1];
}

// Packing solid past this would stack particles off the top of the screen and
// into the wall clamp, which is not a scene anyone will ever make.
function benchCapacity() {
  const d = settings.radius * 2;
  const cols = Math.max(1, Math.floor(W / d));
  const rows = Math.max(1, Math.floor(H / (d * 0.9)));
  return Math.min(MAX_PARTICLES, cols * rows);
}

// Rows at 0.9 diameter and every other row offset: already compacted and
// already overlapping, so the worst case is reached without waiting for a
// tall column of particles to fall and settle.
function benchFill(n) {
  const d = settings.radius * 2;
  const cols = Math.max(1, Math.floor(W / d));
  count = Math.min(n, benchCapacity());
  recycle = 0;
  for (let i = 0; i < count; i++) {
    const row = (i / cols) | 0;
    posX[i] = settings.radius + (i % cols) * d + (row & 1 ? d * 0.5 : 0);
    posY[i] = H - settings.radius - row * d * 0.9;
    prevX[i] = posX[i];
    prevY[i] = posY[i];
  }
}

// Cost is very close to linear in particle count, so the next guess is the
// line through the last two samples solved for the budget (a straight
// proportion on the first). That lands within a few percent in about four
// measurements instead of forty blind ramp steps.
function benchNext(ms) {
  const tried = bench.tried;
  if (tried.length >= BENCH_TRIES) return null;
  if (Math.abs(ms - BENCH_BUDGET) / BENCH_BUDGET < 0.06) return null;

  const b = tried[tried.length - 1];
  const a = tried[tried.length - 2];
  const slope = a && b.n !== a.n ? (b.ms - a.ms) / (b.n - a.n) : 0;

  let guess = slope > 0
    ? b.n + (BENCH_BUDGET - b.ms) / slope
    : bench.n * (BENCH_BUDGET / Math.max(ms, 0.01));

  // A single step never moves more than 4x either way — a wild extrapolation
  // off one noisy sample could otherwise hang the tab for seconds.
  guess = Math.min(Math.max(guess, bench.n * 0.25), bench.n * 4);
  guess = Math.min(Math.max(Math.round(guess / 100) * 100, 100), benchCapacity());
  return tried.some((r) => r.n === guess) ? null : guess;
}

function benchMeasure(n) {
  bench.n = Math.min(Math.max(Math.round(n / 100) * 100, 100), benchCapacity());
  benchFill(bench.n);
  bench.phase = "settle";
  bench.since = performance.now();
  benchStatus.textContent =
    `Testing ${bench.n} particles… (${bench.tried.length + 1}/${BENCH_TRIES})`;
}

function benchTick(now) {
  const wait = bench.phase === "settle" ? BENCH_SETTLE : BENCH_MEASURE;
  if (now - bench.since < wait) return;

  if (bench.phase === "settle") {
    bench.phase = "measure";
    bench.since = now;
    bench.steps.length = 0;
    bench.draws.length = 0;
    return;
  }

  // On a machine slow enough that 900ms holds only a handful of frames, keep
  // going until there are enough samples for the median to mean anything.
  if (bench.steps.length < 8) return;

  const ms = median(bench.steps) + median(bench.draws);
  bench.tried.push({ n: bench.n, ms });

  const next = benchNext(ms);
  if (next === null) benchFinish();
  else benchMeasure(next);
}

function benchStart() {
  stopInput();
  bench.on = true;
  bench.tried.length = 0;
  bench.capBefore = settings.maxParticles;
  settings.maxParticles = MAX_PARTICLES;  // the bench drives count directly
  benchButton.textContent = "Stop benchmark";
  benchApply.style.display = "none";
  benchMeasure(Math.min(2000, benchCapacity()));
}

function benchStop(message) {
  bench.on = false;
  bench.phase = "";
  bench.tried.length = 0;
  settings.maxParticles = bench.capBefore;
  benchButton.textContent = BENCH_LABEL;
  onSettingChanged();  // trims count back under the restored cap
  if (message) benchStatus.textContent = message;
}

function benchFinish() {
  const under = bench.tried.filter((r) => r.ms <= BENCH_BUDGET);
  const best = under.length ? under.reduce((m, r) => (r.n > m.n ? r : m)) : null;
  const points = bench.tried.map((r) => `${r.n}:${r.ms.toFixed(1)}ms`).join("  ");

  benchStop();

  if (!best) {
    benchStatus.textContent =
      `Nothing fits the ${BENCH_BUDGET}ms budget at this quality — ` +
      `lower substeps or passes.\n${points}`;
    return;
  }

  benchResult = {
    n: best.n,
    ms: Math.round(best.ms * 10) / 10,
    substeps: settings.substeps,
    passes: settings.passes,
    radius: settings.radius,
    points,
  };
  try {
    localStorage.setItem(BENCH_KEY, JSON.stringify(benchResult));
  } catch (e) {
    // Private browsing refuses localStorage; the result on screen is enough.
  }
  showBenchResult();
}

function showBenchResult(prefix) {
  const r = benchResult;
  benchStatus.textContent =
    `${prefix || ""}${r.n} particles at ${r.ms}ms of the ${BENCH_BUDGET}ms budget — ` +
    `${r.substeps} substeps, ${r.passes} passes, radius ${r.radius}.` +
    (r.points ? `\n${r.points}` : "");
  benchApply.style.display = "block";
}

const benchHeading = document.createElement("div");
benchHeading.className = "group";
benchHeading.textContent = "Benchmark";

const benchButton = document.createElement("button");
benchButton.className = "wide";
benchButton.textContent = BENCH_LABEL;
benchButton.addEventListener("click", () => {
  if (bench.on) benchStop("Cancelled.");
  else benchStart();
});

const benchApply = document.createElement("button");
benchApply.className = "wide";
benchApply.textContent = "Apply to max particles";
benchApply.style.display = "none";
benchApply.addEventListener("click", () => {
  if (benchResult) setSetting("maxParticles", benchResult.n);
});

const benchStatus = document.createElement("div");
benchStatus.className = "hint";
benchStatus.style.whiteSpace = "pre-line";
benchStatus.textContent =
  "Clears the scene, packs it solid and times the frame. Takes about 10 seconds.";

panelBody.append(benchHeading, benchButton, benchApply, benchStatus);

let benchResult = null;
try {
  benchResult = JSON.parse(localStorage.getItem(BENCH_KEY));
} catch (e) {
  benchResult = null;
}
if (benchResult) showBenchResult("Last run: ");


// -------------------------------------------------------------- main loop

const STEP = 1000 / 60;
const MAX_CATCHUP = 200;
let accumulator = 0;
let lastTime = performance.now();

let frames = 0;
let fpsClock = lastTime;

function frame(now) {
  const dt = Math.min(now - lastTime, MAX_CATCHUP);
  accumulator += dt;
  lastTime = now;

  if (emitting) {
    emitTimer += dt;
    while (emitTimer >= settings.emitInterval) {
      for (let n = 0; n < settings.emitPerBurst; n++) spawn(point.x, point.y);
      emitTimer -= settings.emitInterval;
    }
  }

  // Each placed emitter runs its own clock at its own rate.
  // Skipped during a benchmark run, which owns `count` itself.
  if (objects.length && !bench.on) {
    for (const o of objects) {
      if (o.kind !== "emit") continue;
      o.t += dt;
      while (o.t >= o.interval) {
        for (let n = 0; n < o.burst; n++) spawn(o.x, o.y, o.vx, o.vy, o.spread);
        o.t -= o.interval;
      }
    }
  }

  while (accumulator >= STEP) {
    const t = bench.on ? performance.now() : 0;
    step(STEP / 1000);
    if (bench.on) bench.steps.push(performance.now() - t);
    accumulator -= STEP;
  }

  const drawStart = bench.on ? performance.now() : 0;
  draw();
  if (bench.on) {
    bench.draws.push(performance.now() - drawStart);
    benchTick(now);
  }

  frames++;
  if (now - fpsClock >= 1000) {
    fpsEl.textContent = Math.round((frames * 1000) / (now - fpsClock));
    frames = 0;
    fpsClock = now;
  }
  countEl.textContent = count;

  requestAnimationFrame(frame);
}

// Rotating the iPad fires resize mid-animation; one rAF of settle time keeps
// the new viewport size from being read while it is still changing.
let resizePending = 0;
function scheduleResize() {
  clearTimeout(resizePending);
  resizePending = setTimeout(resizeCanvas, 120);
}
window.addEventListener("resize", scheduleResize);
window.addEventListener("orientationchange", scheduleResize);
if (window.visualViewport) window.visualViewport.addEventListener("resize", scheduleResize);

// A backgrounded tab stops rAF; without this the first frame back would try
// to catch up on minutes of accumulated time (MAX_CATCHUP softens it, but
// resetting the clock is cleaner).
document.addEventListener("visibilitychange", () => {
  // A backgrounded tab makes every timing meaningless, so a run in progress
  // is thrown away rather than reported as a result.
  if (document.hidden && bench.on) benchStop("Cancelled — tab lost focus.");
  if (!document.hidden) {
    lastTime = performance.now();
    accumulator = 0;
    stopInput();
  }
});

resizeCanvas();
updateModeButtons();
requestAnimationFrame(frame);
