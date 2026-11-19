/* Square-marker detector + planar pose for the 4 printed markers (8x8 grid: 2-cell black border + 4x4 code).
   Plain script: works in the browser (window.MarkerDetector) and in Node (module.exports). No dependencies. */
(function (root) {
  'use strict';
  // 1 = black cell, row 0 = top of the printed marker (side with the "▲ MARKER n ▲" label)
  const CODES = {
    1: [[0,0,1,0],[1,0,1,1],[1,0,1,1],[1,0,0,0]],
    2: [[1,0,0,0],[1,0,0,0],[1,0,1,0],[0,1,0,1]],
    3: [[1,0,1,1],[1,0,1,0],[1,1,0,1],[0,0,1,1]],
    4: [[1,1,0,0],[1,1,0,0],[1,0,0,1],[1,0,1,0]],
  };
  const rot = b => b.map((_, i) => b.map((_, j) => b[j][b.length - 1 - i])); // 90° counter-clockwise

  function adaptiveBinary(gray, w, h) {
    const W1 = w + 1, I = new Float64Array(W1 * (h + 1));
    for (let y = 0; y < h; y++) {
      let s = 0;
      for (let x = 0; x < w; x++) { s += gray[y * w + x]; I[(y + 1) * W1 + x + 1] = I[y * W1 + x + 1] + s; }
    }
    const r = Math.max(8, Math.round(Math.min(w, h) / 8));
    const bin = new Uint8Array(w * h);
    for (let y = 0; y < h; y++) {
      const y0 = Math.max(0, y - r), y1 = Math.min(h, y + r + 1);
      for (let x = 0; x < w; x++) {
        const x0 = Math.max(0, x - r), x1 = Math.min(w, x + r + 1);
        const m = (I[y1 * W1 + x1] - I[y0 * W1 + x1] - I[y1 * W1 + x0] + I[y0 * W1 + x0]) / ((x1 - x0) * (y1 - y0));
        bin[y * w + x] = gray[y * w + x] < m - Math.max(6, 0.08 * m) ? 1 : 0;
      }
    }
    return bin;
  }

  function hull(pts) { // Andrew monotone chain, pts: array of [x,y]
    pts.sort((a, b) => a[0] - b[0] || a[1] - b[1]);
    const cr = (o, a, b) => (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0]);
    const lo = [], up = [];
    for (const p of pts) { while (lo.length >= 2 && cr(lo[lo.length - 2], lo[lo.length - 1], p) <= 0) lo.pop(); lo.push(p); }
    for (let i = pts.length - 1; i >= 0; i--) { const p = pts[i]; while (up.length >= 2 && cr(up[up.length - 2], up[up.length - 1], p) <= 0) up.pop(); up.push(p); }
    up.pop(); lo.pop(); return lo.concat(up);
  }
  const polyArea = P => { let a = 0; for (let i = 0; i < P.length; i++) { const p = P[i], q = P[(i + 1) % P.length]; a += p[0] * q[1] - q[0] * p[1]; } return a / 2; };

  function quadFromHull(H) {
    let cx = 0, cy = 0; for (const p of H) { cx += p[0]; cy += p[1]; } cx /= H.length; cy /= H.length;
    const d2 = (a, b) => (a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2;
    let p0 = H[0]; for (const p of H) if (d2(p, [cx, cy]) > d2(p0, [cx, cy])) p0 = p;
    let p2 = H[0]; for (const p of H) if (d2(p, p0) > d2(p2, p0)) p2 = p;
    const side = p => (p2[0] - p0[0]) * (p[1] - p0[1]) - (p2[1] - p0[1]) * (p[0] - p0[0]);
    let p1 = null, p3 = null, s1 = 0, s3 = 0;
    for (const p of H) { const s = side(p); if (s > s1) { s1 = s; p1 = p; } if (s < s3) { s3 = s; p3 = p; } }
    if (!p1 || !p3) return null;
    let q = [p0, p1, p2, p3];
    if (polyArea(q) < 0) q = [p0, p3, p2, p1]; // clockwise on screen (y down) => positive shoelace
    return q.map(p => [p[0], p[1]]);
  }

  function refineCorners(q, bnd) { // fit a line to boundary pixels along each side, intersect
    const lines = [];
    for (let i = 0; i < 4; i++) {
      const a = q[i], b = q[(i + 1) % 4], dx = b[0] - a[0], dy = b[1] - a[1], L = Math.hypot(dx, dy);
      const nx = -dy / L, ny = dx / L, tol = Math.max(2, 0.04 * L);
      let n = 0, sx = 0, sy = 0, sxx = 0, syy = 0, sxy = 0;
      for (let k = 0; k < bnd.length; k += 2) {
        const px = bnd[k], py = bnd[k + 1];
        const t = ((px - a[0]) * dx + (py - a[1]) * dy) / (L * L);
        if (t < 0.12 || t > 0.88) continue;
        if (Math.abs((px - a[0]) * nx + (py - a[1]) * ny) > tol) continue;
        n++; sx += px; sy += py; sxx += px * px; syy += py * py; sxy += px * py;
      }
      if (n < 6) return q;
      const mx = sx / n, my = sy / n, cxx = sxx / n - mx * mx, cyy = syy / n - my * my, cxy = sxy / n - mx * my;
      const ang = 0.5 * Math.atan2(2 * cxy, cxx - cyy); // direction of max variance
      lines.push({ px: mx, py: my, dx: Math.cos(ang), dy: Math.sin(ang) });
    }
    const out = [];
    for (let i = 0; i < 4; i++) {
      const l1 = lines[(i + 3) % 4], l2 = lines[i];
      const det = l1.dx * l2.dy - l1.dy * l2.dx; if (Math.abs(det) < 1e-6) return q;
      const t = ((l2.px - l1.px) * l2.dy - (l2.py - l1.py) * l2.dx) / det;
      const p = [l1.px + t * l1.dx, l1.py + t * l1.dy];
      if (Math.hypot(p[0] - q[i][0], p[1] - q[i][1]) > 0.15 * Math.hypot(q[1][0] - q[0][0], q[1][1] - q[0][1]) + 3) return q;
      out.push(p);
    }
    return out;
  }

  // homography mapping src points (4) to dst points (4); returns 3x3 row-major array
  function homography(src, dst) {
    const A = [], B = [];
    for (let i = 0; i < 4; i++) {
      const [x, y] = src[i], [u, v] = dst[i];
      A.push([x, y, 1, 0, 0, 0, -u * x, -u * y]); B.push(u);
      A.push([0, 0, 0, x, y, 1, -v * x, -v * y]); B.push(v);
    }
    const n = 8; // gaussian elimination
    for (let c = 0; c < n; c++) {
      let p = c; for (let r = c + 1; r < n; r++) if (Math.abs(A[r][c]) > Math.abs(A[p][c])) p = r;
      [A[c], A[p]] = [A[p], A[c]]; [B[c], B[p]] = [B[p], B[c]];
      if (Math.abs(A[c][c]) < 1e-12) return null;
      for (let r = 0; r < n; r++) if (r !== c) { const f = A[r][c] / A[c][c]; for (let k = c; k < n; k++) A[r][k] -= f * A[c][k]; B[r] -= f * B[c]; }
    }
    const h = B.map((b, i) => b / A[i][i]);
    return [h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7], 1];
  }
  const applyH = (H, x, y) => { const w = H[6] * x + H[7] * y + H[8]; return [(H[0] * x + H[1] * y + H[2]) / w, (H[3] * x + H[4] * y + H[5]) / w]; };

  function sampleGrid(gray, w, h, q) {
    const H = homography([[0, 0], [1, 0], [1, 1], [0, 1]], q); if (!H) return null;
    const bil = (x, y) => {
      if (x < 0 || y < 0 || x >= w - 1 || y >= h - 1) return -1;
      const x0 = x | 0, y0 = y | 0, fx = x - x0, fy = y - y0, i = y0 * w + x0;
      return gray[i] * (1 - fx) * (1 - fy) + gray[i + 1] * fx * (1 - fy) + gray[i + w] * (1 - fx) * fy + gray[i + w + 1] * fx * fy;
    };
    const v = [];
    for (let r = 0; r < 8; r++) for (let c = 0; c < 8; c++) {
      let s = 0;
      for (let a = -1; a <= 1; a++) for (let b = -1; b <= 1; b++) {
        const [x, y] = applyH(H, (c + 0.5 + 0.22 * b) / 8, (r + 0.5 + 0.22 * a) / 8);
        const g = bil(x, y); if (g < 0) return null; s += g;
      }
      v.push(s / 9);
    }
    return v;
  }

  function decode(vals) {
    const mn = Math.min(...vals), mx = Math.max(...vals);
    if (mx - mn < 25) return null;
    const thr = (mn + mx) / 2;
    const cell = (r, c) => vals[r * 8 + c] < thr ? 1 : 0;
    let borderWhite = 0;
    for (let r = 0; r < 8; r++) for (let c = 0; c < 8; c++)
      if ((r < 2 || r > 5 || c < 2 || c > 5) && !cell(r, c)) borderWhite++;
    if (borderWhite > 3) return null;
    let b = [0, 1, 2, 3].map(r => [0, 1, 2, 3].map(c => cell(r + 2, c + 2)));
    let best = null;
    for (let k = 0; k < 4; k++) {
      for (const id in CODES) {
        let d = 0; const C = CODES[id];
        for (let r = 0; r < 4; r++) for (let c = 0; c < 4; c++) d += b[r][c] !== C[r][c];
        if (!best || d < best.d) best = { id: +id, k, d };
      }
      b = rot(b);
    }
    return best && best.d <= 2 ? best : null;
  }

  function detect(gray, w, h, opt) {
    opt = opt || {};
    const minSide = opt.minSide || Math.max(16, Math.round(Math.min(w, h) * 0.04));
    const bin = adaptiveBinary(gray, w, h);
    const lab = new Int32Array(w * h), stack = new Int32Array(w * h);
    const found = [];
    let label = 0;
    for (let start = 0; start < w * h; start++) {
      if (!bin[start] || lab[start]) continue;
      label++;
      let sp = 0; stack[sp++] = start; lab[start] = label;
      let area = 0, minx = w, maxx = 0, miny = h, maxy = 0, touches = false;
      const bnd = [];
      while (sp) {
        const p = stack[--sp], x = p % w, y = (p / w) | 0;
        area++;
        if (x < minx) minx = x; if (x > maxx) maxx = x; if (y < miny) miny = y; if (y > maxy) maxy = y;
        if (x === 0 || y === 0 || x === w - 1 || y === h - 1) { touches = true; bnd.push(x, y); continue; }
        let edge = false;
        const nb = [p - 1, p + 1, p - w, p + w];
        for (const n of nb) {
          if (bin[n]) { if (!lab[n]) { lab[n] = label; stack[sp++] = n; } }
          else edge = true;
        }
        if (edge) bnd.push(x, y);
      }
      const bw = maxx - minx, bh = maxy - miny;
      if (touches || bw < minSide || bh < minSide || area < minSide * minSide * 0.25) continue;
      if (bw > 0.98 * w && bh > 0.98 * h) continue;
      const pts = []; for (let k = 0; k < bnd.length; k += 2) pts.push([bnd[k], bnd[k + 1]]);
      const Hh = hull(pts); if (Hh.length < 4) continue;
      let q = quadFromHull(Hh); if (!q) continue;
      const ha = Math.abs(polyArea(Hh)), qa = polyArea(q);
      if (qa < 0.88 * ha) continue;                       // hull must be (nearly) a quadrilateral
      const sides = q.map((p, i) => Math.hypot(q[(i + 1) % 4][0] - p[0], q[(i + 1) % 4][1] - p[1]));
      if (Math.min(...sides) < minSide * 0.7 || Math.min(...sides) < 0.25 * Math.max(...sides)) continue;
      q = refineCorners(q, bnd);
      const vals = sampleGrid(gray, w, h, q); if (!vals) continue;
      const dec = decode(vals); if (!dec) continue;
      const k = dec.k, corners = [0, 1, 2, 3].map(i => q[(i + k) % 4]); // TL, TR, BR, BL of the printed marker
      found.push({ id: dec.id, corners, err: dec.d, area: qa });
    }
    // keep the largest detection per id
    const best = {};
    for (const m of found) if (!best[m.id] || m.area > best[m.id].area) best[m.id] = m;
    return Object.values(best);
  }

  // ---------- pose ----------
  // size = black square width (m); f, cx, cy in the same pixels as corners.
  // returns { R: 3x3 rows, t: [x,y,z] } in OpenCV camera coords (x right, y down, z forward);
  // marker frame: X = right edge, Y = towards the top (label) edge, Z = out of the paper.
  function pose(corners, size, f, cx, cy) {
    const s = size / 2;
    const H = homography([[-s, s], [s, s], [s, -s], [-s, -s]], corners); if (!H) return null;
    const col = j => [(H[j] - cx * H[6 + j]) / f, (H[3 + j] - cy * H[6 + j]) / f, H[6 + j]];
    let h1 = col(0), h2 = col(1), h3 = col(2);
    const n = v => Math.hypot(v[0], v[1], v[2]);
    let lam = 2 / (n(h1) + n(h2)); if (h3[2] * lam < 0) lam = -lam;
    const sc = (v, k) => v.map(x => x * k), add = (a, b) => a.map((x, i) => x + b[i]), sub = (a, b) => a.map((x, i) => x - b[i]);
    const cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
    const nz = v => sc(v, 1 / n(v));
    const x = nz(sc(h1, lam)), y = nz(sc(h2, lam));
    const a = nz(add(x, y)), b = nz(sub(x, y));
    const r1 = sc(add(a, b), Math.SQRT1_2), r2 = sc(sub(a, b), Math.SQRT1_2), r3 = cross(r1, r2);
    const t = sc(h3, lam);
    return { R: [[r1[0], r2[0], r3[0]], [r1[1], r2[1], r3[1]], [r1[2], r2[2], r3[2]]], t };
  }

  // focal length estimate from one marker (pixels), or null when ill-conditioned
  function estimateFocal(corners, cx, cy) {
    const H = homography([[-1, 1], [1, 1], [1, -1], [-1, -1]], corners.map(p => [p[0] - cx, p[1] - cy])); if (!H) return null;
    const h11 = H[0], h12 = H[1], h21 = H[3], h22 = H[4], h31 = H[6], h32 = H[7];
    const a1 = h11 * h12 + h21 * h22, b1 = h31 * h32;
    const a2 = h11 * h11 + h21 * h21 - h12 * h12 - h22 * h22, b2 = h31 * h31 - h32 * h32;
    const den = -(a1 * b1 + a2 * b2), num = b1 * b1 + b2 * b2;
    // w = 1/f^2 minimizing (a w + b)^2  ->  w = -(a·b)/(a·a)  (written as f^2 = -(a·a)/(a·b))
    const aa = a1 * a1 + a2 * a2, ab = a1 * b1 + a2 * b2;
    if (ab >= 0 || num < 1e-14) return null;
    const f2 = -aa / ab; if (!(f2 > 0)) return null;
    return Math.sqrt(f2);
  }


  // least-squares homography (N >= 4 points) with Hartley normalisation; returns 3x3 row-major
  function homographyLS(src, dst) {
    const norm = P => { let mx = 0, my = 0; for (const p of P) { mx += p[0]; my += p[1]; } mx /= P.length; my /= P.length;
      let d = 0; for (const p of P) d += Math.hypot(p[0] - mx, p[1] - my); d = d / P.length || 1; const k = Math.SQRT2 / d;
      return { T: [k, 0, -k * mx, 0, k, -k * my, 0, 0, 1], P: P.map(p => [k * (p[0] - mx), k * (p[1] - my)]) }; };
    const a = norm(src), b = norm(dst);
    const AtA = Array.from({ length: 8 }, () => new Float64Array(8)), Atb = new Float64Array(8);
    for (let i = 0; i < src.length; i++) {
      const [x, y] = a.P[i], [u, v] = b.P[i];
      const rows = [[x, y, 1, 0, 0, 0, -u * x, -u * y, u], [0, 0, 0, x, y, 1, -v * x, -v * y, v]];
      for (const r of rows) for (let p = 0; p < 8; p++) { Atb[p] += r[p] * r[8]; for (let q = 0; q < 8; q++) AtA[p][q] += r[p] * r[q]; }
    }
    const A = AtA.map(r => Array.from(r)), B = Array.from(Atb), n = 8;
    for (let c = 0; c < n; c++) {
      let p = c; for (let r = c + 1; r < n; r++) if (Math.abs(A[r][c]) > Math.abs(A[p][c])) p = r;
      [A[c], A[p]] = [A[p], A[c]]; [B[c], B[p]] = [B[p], B[c]];
      if (Math.abs(A[c][c]) < 1e-12) return null;
      for (let r = 0; r < n; r++) if (r !== c) { const f = A[r][c] / A[c][c]; for (let k = c; k < n; k++) A[r][k] -= f * A[c][k]; B[r] -= f * B[c]; }
    }
    const h = B.map((v, i) => v / A[i][i]); const Hn = [...h, 1];
    // H = Tb^-1 * Hn * Ta
    const mul = (X, Y) => { const Z = new Array(9).fill(0); for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) for (let k = 0; k < 3; k++) Z[i * 3 + j] += X[i * 3 + k] * Y[k * 3 + j]; return Z; };
    const kb = b.T[0], Tbi = [1 / kb, 0, -b.T[2] / kb, 0, 1 / kb, -b.T[5] / kb, 0, 0, 1];
    const H = mul(mul(Tbi, Hn), a.T);
    return H.map(v => v / H[8]);
  }
  function poseFromH(H, f, cx, cy) {
    const col = j => [(H[j] - cx * H[6 + j]) / f, (H[3 + j] - cy * H[6 + j]) / f, H[6 + j]];
    const h1 = col(0), h2 = col(1), h3 = col(2);
    const n = v => Math.hypot(v[0], v[1], v[2]);
    let lam = 2 / (n(h1) + n(h2)); if (h3[2] * lam < 0) lam = -lam;
    const sc = (v, k) => v.map(x => x * k), add = (a, b) => a.map((x, i) => x + b[i]), sub = (a, b) => a.map((x, i) => x - b[i]);
    const cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
    const nz = v => sc(v, 1 / n(v));
    const x = nz(sc(h1, lam)), y = nz(sc(h2, lam)), a = nz(add(x, y)), b = nz(sub(x, y));
    const r1 = sc(add(a, b), Math.SQRT1_2), r2 = sc(sub(a, b), Math.SQRT1_2), r3 = cross(r1, r2);
    return { R: [[r1[0], r2[0], r3[0]], [r1[1], r2[1], r3[1]], [r1[2], r2[2], r3[2]]], t: sc(h3, lam) };
  }
  // pose of a plane from N >= 4 correspondences: obj = [[X,Y],...] (m, plane frame), img = [[u,v],...] (px)
  function posePlane(obj, img, f, cx, cy) { const H = homographyLS(obj, img); return H ? poseFromH(H, f, cx, cy) : null; }
  // focal from a plane homography (any number of points); null when ill-conditioned
  function focalPlane(obj, img, cx, cy) {
    const H = homographyLS(obj, img.map(p => [p[0] - cx, p[1] - cy])); if (!H) return null;
    const h11 = H[0], h12 = H[1], h21 = H[3], h22 = H[4], h31 = H[6], h32 = H[7];
    const a1 = h11 * h12 + h21 * h22, b1 = h31 * h32, a2 = h11 * h11 + h21 * h21 - h12 * h12 - h22 * h22, b2 = h31 * h31 - h32 * h32;
    const aa = a1 * a1 + a2 * a2, ab = a1 * b1 + a2 * b2;
    if (ab >= 0) return null; const f2 = -aa / ab; return f2 > 0 ? Math.sqrt(f2) : null;
  }

  const api = { detect, pose, estimateFocal, homography, homographyLS, posePlane, focalPlane, CODES };
  if (typeof module !== 'undefined' && module.exports) module.exports = api; else root.MarkerDetector = api;
})(typeof window !== 'undefined' ? window : globalThis);
