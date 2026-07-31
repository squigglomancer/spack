// ---------- Tunable constants ----------
const NODE_LIMIT = 300000;   // safety cap on solver search per attempt
const GEN_TIME_BUDGET_MS = 15000;

let solution, locked, grid, boardOutcomeClue, lineClues, currentDifficulty, metaOutcome, metaMessage;
let celebrating = false, wonAlready = false, celebrationToken = 0;
let cellElements, edgeBoxes;
let isDailyMode = false;
let moveHistory = [];
let redoStack = [];
let displayedViolations = [[false, false, false], [false, false, false], [false, false, false]];
let pendingViolationTimers = [[null, null, null], [null, null, null], [null, null, null]];
let displayedRowViolations = Array(9).fill(false), displayedColViolations = Array(9).fill(false);
let pendingRowViolationTimers = Array(9).fill(null), pendingColViolationTimers = Array(9).fill(null);

function resetViolationState() {
  for (let sr = 0; sr < 3; sr++) {
    for (let sc = 0; sc < 3; sc++) {
      if (pendingViolationTimers[sr][sc]) clearTimeout(pendingViolationTimers[sr][sc]);
      pendingViolationTimers[sr][sc] = null;
      displayedViolations[sr][sc] = false;
    }
  }
  for (let i = 0; i < 9; i++) {
    if (pendingRowViolationTimers[i]) clearTimeout(pendingRowViolationTimers[i]);
    if (pendingColViolationTimers[i]) clearTimeout(pendingColViolationTimers[i]);
    pendingRowViolationTimers[i] = null;
    pendingColViolationTimers[i] = null;
    displayedRowViolations[i] = false;
    displayedColViolations[i] = false;
  }
}

// ---------- RNG (swappable: Math.random for practice, seeded for daily) ----------
let rng = Math.random;

// xmur3 string hash -> 32-bit seed, then mulberry32 as the actual stream.
// Same string in -> exact same sequence of "random" numbers out, so every
// visitor's browser generates the identical puzzle for a given seed.
function xmur3(str) {
  let h = 1779033703 ^ str.length;
  for (let i = 0; i < str.length; i++) {
    h = Math.imul(h ^ str.charCodeAt(i), 3432918353);
    h = (h << 13) | (h >>> 19);
  }
  return function () {
    h = Math.imul(h ^ (h >>> 16), 2246822507);
    h = Math.imul(h ^ (h >>> 13), 3266489909);
    return (h ^= h >>> 16) >>> 0;
  };
}
function mulberry32(seed) {
  let a = seed;
  return function () {
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
function makeSeededRng(seedString) {
  return mulberry32(xmur3(seedString)());
}

// ---------- basic helpers ----------
function shuffle(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(rng() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

function combinations(arr, k) {
  const result = [];
  function helper(start, combo) {
    if (combo.length === k) { result.push(combo.slice()); return; }
    for (let i = start; i < arr.length; i++) {
      combo.push(arr[i]);
      helper(i + 1, combo);
      combo.pop();
    }
  }
  helper(0, []);
  return result;
}

const LINES = [
  [0, 1, 2], [3, 4, 5], [6, 7, 8],
  [0, 3, 6], [1, 4, 7], [2, 5, 8],
  [0, 4, 8], [2, 4, 6],
];

// cells: length-9 row-major array of 'X'/'O'. Returns 'X'|'O'|'draw'|'void'
function boardWinner(cells) {
  const hasLine = (sym) => LINES.some((line) => line.every((i) => cells[i] === sym));
  const xWin = hasLine('X');
  const oWin = hasLine('O');
  if (xWin && oWin) return 'void';
  if (xWin) return 'X';
  if (oWin) return 'O';
  return 'draw';
}

function localRowColXCounts(cells) {
  const rowX = [0, 0, 0], colX = [0, 0, 0];
  for (let r = 0; r < 3; r++) {
    for (let c = 0; c < 3; c++) {
      if (cells[r * 3 + c] === 'X') { rowX[r]++; colX[c]++; }
    }
  }
  return { rowX, colX };
}

function getBoardCells(g, sr, sc) {
  const cells = [];
  for (let r = 0; r < 3; r++) for (let c = 0; c < 3; c++) cells.push(g[sr * 3 + r][sc * 3 + c]);
  return cells;
}

// ---------- solution generation ----------
// Rule (open, not hidden): a board may never have 6 or more of either
// symbol — equivalently, every board ends up 4-5 or 5-4, but which one is
// just whatever falls out, not a pre-chosen target.
function generateRandomSolutionAttempt() {
  const sol = Array.from({ length: 9 }, () => Array(9).fill(''));
  for (let sr = 0; sr < 3; sr++) {
    for (let sc = 0; sc < 3; sc++) {
      let cells;
      for (let tries = 0; tries < 500; tries++) {
        cells = Array.from({ length: 9 }, () => (rng() < 0.5 ? 'X' : 'O'));
        const xCount = cells.filter((v) => v === 'X').length;
        if (xCount > 5 || (9 - xCount) > 5) continue; // neither symbol may reach 6
        if (boardWinner(cells) !== 'void') break; // can't have both an X line and an O line
      }
      for (let r = 0; r < 3; r++) for (let c = 0; c < 3; c++) sol[sr * 3 + r][sc * 3 + c] = cells[r * 3 + c];
    }
  }
  return sol;
}

// Each of the 9 boards' own winner ('X'/'O'/'draw'), row-major over the
// super-board — the "cells" the meta-board is judged on.
function getBoardWinners(sol) {
  const winners = [];
  for (let sr = 0; sr < 3; sr++) for (let sc = 0; sc < 3; sc++) winners.push(boardWinner(getBoardCells(sol, sr, sc)));
  return winners;
}

// The meta-board: look for a line of three boards won by the same symbol —
// same win-detection logic as boardWinner, just one level up. 'void' means
// both an X-line and an O-line of boards exist simultaneously, which (like
// a void board) is thrown out rather than shown to the player.
function metaWinner(sol) {
  return boardWinner(getBoardWinners(sol));
}

// Flavor-text pools for the always-visible meta-board reveal — one is
// chosen at random (via the puzzle's rng, so it's fixed once per puzzle and
// stable across re-renders/reloads) per generated puzzle.
const META_MESSAGES = {
  X: [
    "The X's have this one",
    "Hey man, it's X's game!",
    "O... didn't stand a chance",
    "I'd bet on X if I were you",
    "The O's are history",
    "X.X <--- what the O's look like right about now",
    'X wins yet again...',
  ],
  O: [
    "This is O's game",
    "The O's have it",
    'This is an O board',
    'OOO000OOOooooo',
    'O wins this one',
    'My money is on O',
  ],
  draw: [
    "It's a cat's game!",
    "It's a dang tie!",
    "It's nobody's game",
    'Nessuno ha vinto',
    'Looks like a draw',
    "It's a wash",
    "It's a total stalemate",
  ],
};

function pickMetaMessage(outcome) {
  const pool = META_MESSAGES[outcome];
  if (!pool) return null;
  return pool[Math.floor(rng() * pool.length)];
}

// Rejects and retries whole solutions that either (a) have a void
// meta-board outcome (~5% of attempts) or (b) let one symbol win 6+ of the
// 9 boards (~22% of attempts, mostly non-overlapping with (a)) — the same
// "at most 5 of either symbol" idea as generateRandomSolutionAttempt's
// per-board rule, just one level up. Combined, roughly 3 in 4 attempts pass
// on the first try. Everything else about board generation is unchanged.
function generateRandomSolution() {
  let sol;
  for (let attempt = 0; attempt < 2000; attempt++) {
    sol = generateRandomSolutionAttempt();
    const winners = getBoardWinners(sol);
    if (boardWinner(winners) === 'void') continue;
    const xBoards = winners.filter((w) => w === 'X').length;
    const oBoards = winners.filter((w) => w === 'O').length;
    if (xBoards > 5 || oBoards > 5) continue;
    return sol;
  }
  return sol; // exceedingly unlikely fallback — last attempt's invalid solution
}

function countLineSymbol(g, type, index, sym) {
  let count = 0;
  if (type === 'row') for (let c = 0; c < 9; c++) { if (g[index][c] === sym) count++; }
  else for (let r = 0; r < 9; r++) { if (g[r][index] === sym) count++; }
  return count;
}
function countLineX(sol, type, index) { return countLineSymbol(sol, type, index, 'X'); }
function lineCellCoords(type, index) {
  const coords = [];
  if (type === 'row') for (let c = 0; c < 9; c++) coords.push([index, c]);
  else for (let r = 0; r < 9; r++) coords.push([r, index]);
  return coords;
}

// ---------- solver: given locked cells + all clue constraints, count solutions up to maxCount ----------
let candidateCache = new Map();

function boardLocalKey(sr, sc) {
  let key = '';
  for (let r = 0; r < 3; r++) {
    for (let c = 0; c < 3; c++) {
      const gr = sr * 3 + r, gc = sc * 3 + c;
      key += locked[gr][gc] ? grid[gr][gc] : '_';
    }
  }
  return sr + ',' + sc + ',' + (boardOutcomeClue[sr][sc] || '-') + ',' + key;
}

function buildBoardCandidates(sr, sc) {
  const key = boardLocalKey(sr, sc);
  const cached = candidateCache.get(key);
  if (cached) return cached;

  const fixed = [];
  const freePositions = [];
  for (let r = 0; r < 3; r++) {
    for (let c = 0; c < 3; c++) {
      const gr = sr * 3 + r, gc = sc * 3 + c, pos = r * 3 + c;
      if (locked[gr][gc]) fixed.push({ pos, val: grid[gr][gc] });
      else freePositions.push(pos);
    }
  }
  const lockedX = fixed.filter((f) => f.val === 'X').length;
  const lockedO = fixed.length - lockedX;
  const k = freePositions.length;
  // Neither symbol's final count may exceed 5.
  const minXFree = Math.max(0, k - (5 - lockedO));
  const maxXFree = Math.min(k, 5 - lockedX);
  const requiredOutcome = boardOutcomeClue[sr][sc];
  const candidates = [];
  for (let xFree = minXFree; xFree <= maxXFree; xFree++) {
    for (const xPositions of combinations(freePositions, xFree)) {
      const cells = new Array(9).fill(null);
      for (const f of fixed) cells[f.pos] = f.val;
      for (const p of freePositions) cells[p] = xPositions.includes(p) ? 'X' : 'O';
      const winner = boardWinner(cells);
      if (winner === 'void') continue; // illegal: can't have both an X line and an O line
      if (requiredOutcome && winner !== requiredOutcome) continue; // must match the given board outcome
      const { rowX, colX } = localRowColXCounts(cells);
      candidates.push({ cells, winner, rowX, colX });
    }
  }
  candidateCache.set(key, candidates);
  return candidates;
}

// Diagnostic utility only — no longer used by live generation (see the
// comment in generatePuzzle). Handy for cross-checking via the console.
function countSolutions(maxCount, nodeLimit) {
  const limit = nodeLimit ?? NODE_LIMIT;
  const candsByBoard = [];
  for (let sr = 0; sr < 3; sr++) {
    candsByBoard[sr] = [];
    for (let sc = 0; sc < 3; sc++) candsByBoard[sr][sc] = buildBoardCandidates(sr, sc);
  }

  // Row-clue targets, indexed [sr][localRow]; null where no clue exists.
  const rowTarget = [[null, null, null], [null, null, null], [null, null, null]];
  // Column-clue targets, indexed [sc][localCol]; null where no clue exists.
  const colTarget = [[null, null, null], [null, null, null], [null, null, null]];
  for (const clue of lineClues) {
    if (clue.type === 'row') rowTarget[Math.floor(clue.index / 3)][clue.index % 3] = clue.targetX;
    else colTarget[Math.floor(clue.index / 3)][clue.index % 3] = clue.targetX;
  }

  let count = 0, nodes = 0, exceeded = false;
  let rowRunning = [0, 0, 0];              // resets at the start of each super-row band
  const colRunning = [[0, 0, 0], [0, 0, 0], [0, 0, 0]]; // persists across the whole search, indexed [sc][localCol]

  function recurse(boardIdx) {
    if (count >= maxCount || exceeded) return;
    nodes++;
    if (nodes > limit) { exceeded = true; return; }
    if (boardIdx === 9) { count++; return; }

    const sr = Math.floor(boardIdx / 3), sc = boardIdx % 3;
    if (sc === 0) rowRunning = [0, 0, 0];
    const prevRowRunning = rowRunning.slice();
    const prevColRunning = colRunning[sc].slice();

    for (const cand of candsByBoard[sr][sc]) {
      let ok = true;
      for (let k = 0; k < 3; k++) {
        const nr = prevRowRunning[k] + cand.rowX[k];
        const nc = prevColRunning[k] + cand.colX[k];
        if (rowTarget[sr][k] !== null) {
          const remaining = 2 - sc;
          if (nr > rowTarget[sr][k] || nr + 3 * remaining < rowTarget[sr][k]) { ok = false; break; }
        }
        if (colTarget[sc][k] !== null) {
          const remaining = 2 - sr;
          if (nc > colTarget[sc][k] || nc + 3 * remaining < colTarget[sc][k]) { ok = false; break; }
        }
        rowRunning[k] = nr;
        colRunning[sc][k] = nc;
      }
      if (ok) recurse(boardIdx + 1);
      rowRunning = prevRowRunning.slice();
      colRunning[sc] = prevColRunning.slice();
      if (count >= maxCount || exceeded) return;
    }
  }
  recurse(0);
  return { count, exceeded };
}

// ---------- named deduction rules, cheapest first ----------
// Each rule scans the current (scratch) locked/grid state and fills in any
// cell it can prove is forced by that rule alone, returning whether it made
// progress. Difficulty tiers allow different subsets of these rules — a
// puzzle is only "easy" if it can be fully solved using easy's rules alone.

// Rule: a board already has 5 of one symbol placed (the open max for any
// board) -> every remaining empty cell in that board must be the other
// symbol.
function ruleMaxCapExhaustion() {
  let changed = false;
  for (let sr = 0; sr < 3; sr++) {
    for (let sc = 0; sc < 3; sc++) {
      const { x, o } = boardSymbolCounts(sr, sc);
      const forced = x === 5 ? 'O' : (o === 5 ? 'X' : null);
      if (!forced) continue;
      for (let r = 0; r < 3; r++) {
        for (let c = 0; c < 3; c++) {
          const gr = sr * 3 + r, gc = sc * 3 + c;
          if (!locked[gr][gc]) { locked[gr][gc] = true; grid[gr][gc] = forced; changed = true; }
        }
      }
    }
  }
  return changed;
}

// Rule: a clued row/column already has its full quota of X (or O) placed ->
// every remaining empty cell in that line must be the other symbol.
function ruleLineExhaustion() {
  let changed = false;
  for (const clue of lineClues) {
    const targetO = 9 - clue.targetX;
    const curX = countLineSymbol(grid, clue.type, clue.index, 'X');
    const curO = countLineSymbol(grid, clue.type, clue.index, 'O');
    const forced = curX === clue.targetX ? 'O' : (curO === targetO ? 'X' : null);
    if (!forced) continue;
    for (const [r, c] of lineCellCoords(clue.type, clue.index)) {
      if (!locked[r][c]) { locked[r][c] = true; grid[r][c] = forced; changed = true; }
    }
  }
  return changed;
}

// Rule 3: within-board outcome forcing. For a board whose winner is known,
// use its full local candidate set (already respects split + outcome) — if
// every remaining valid local completion agrees on a cell, it's forced.
// This only ever uses that one board's own cells; it never looks elsewhere.
function ruleOutcomeLocal() {
  let changed = false;
  for (let sr = 0; sr < 3; sr++) {
    for (let sc = 0; sc < 3; sc++) {
      if (!boardOutcomeClue[sr][sc]) continue;
      const cands = buildBoardCandidates(sr, sc);
      if (cands.length === 0) continue;
      for (let i = 0; i < 9; i++) {
        const gr = sr * 3 + Math.floor(i / 3), gc = sc * 3 + (i % 3);
        if (locked[gr][gc]) continue;
        const firstVal = cands[0].cells[i];
        if (cands.every((cand) => cand.cells[i] === firstVal)) {
          locked[gr][gc] = true; grid[gr][gc] = firstVal; changed = true;
        }
      }
    }
  }
  return changed;
}

// A board's true winner is knowable once a line is complete among its
// LOCKED cells — a given outcome badge, or a line formed purely from cells
// already placed. The "no void boards" invariant guarantees that once a
// line locks in, nothing else is possible for that board, even before every
// cell in it is filled. Returns null if not yet determinable.
function boardSettledWinner(sr, sc) {
  if (boardOutcomeClue[sr][sc]) return boardOutcomeClue[sr][sc];
  const cells = getBoardCells(grid, sr, sc);
  const hasLine = (sym) => LINES.some((line) => line.every((i) => cells[i] === sym));
  if (hasLine('X')) return 'X';
  if (hasLine('O')) return 'O';
  for (let r = 0; r < 3; r++) for (let c = 0; c < 3; c++) if (!locked[sr * 3 + r][sc * 3 + c]) return null;
  return 'draw';
}

// Same candidate-building as buildBoardCandidates, but filters out any of
// `excluded` as a possible winner instead of requiring an exact match.
// Deliberately uncached (unlike buildBoardCandidates) since it's only ever
// called for boards without a boardOutcomeClue, where the exclusion set is
// derived fresh each call from the meta rules below — a 3x3 board's
// candidate space is cheap enough that this doesn't need memoizing.
function buildBoardCandidatesExcluding(sr, sc, excluded) {
  const fixed = [];
  const freePositions = [];
  for (let r = 0; r < 3; r++) {
    for (let c = 0; c < 3; c++) {
      const gr = sr * 3 + r, gc = sc * 3 + c, pos = r * 3 + c;
      if (locked[gr][gc]) fixed.push({ pos, val: grid[gr][gc] });
      else freePositions.push(pos);
    }
  }
  const lockedX = fixed.filter((f) => f.val === 'X').length;
  const lockedO = fixed.length - lockedX;
  const k = freePositions.length;
  const minXFree = Math.max(0, k - (5 - lockedO));
  const maxXFree = Math.min(k, 5 - lockedX);
  const candidates = [];
  for (let xFree = minXFree; xFree <= maxXFree; xFree++) {
    for (const xPositions of combinations(freePositions, xFree)) {
      const cells = new Array(9).fill(null);
      for (const f of fixed) cells[f.pos] = f.val;
      for (const p of freePositions) cells[p] = xPositions.includes(p) ? 'X' : 'O';
      const winner = boardWinner(cells);
      if (winner === 'void') continue;
      if (excluded.includes(winner)) continue;
      candidates.push({ cells, winner });
    }
  }
  return candidates;
}

function forceBoardCellsExcluding(sr, sc, excluded) {
  if (excluded.length === 0) return false;
  const cands = buildBoardCandidatesExcluding(sr, sc, excluded);
  if (cands.length === 0) return false; // conservative — shouldn't happen from a consistent state
  let changed = false;
  for (let i = 0; i < 9; i++) {
    const gr = sr * 3 + Math.floor(i / 3), gc = sc * 3 + (i % 3);
    if (locked[gr][gc]) continue;
    const firstVal = cands[0].cells[i];
    if (cands.every((cand) => cand.cells[i] === firstVal)) {
      locked[gr][gc] = true; grid[gr][gc] = firstVal; changed = true;
    }
  }
  return changed;
}

// Rule: meta-cap exhaustion. Mirrors ruleMaxCapExhaustion one level up — if
// 5 of the 9 boards are already settled to one symbol (the open max, same
// as the per-board cap), no other board can be that symbol.
function ruleMetaCapExhaustion() {
  let xSettled = 0, oSettled = 0;
  const settled = [];
  for (let sr = 0; sr < 3; sr++) for (let sc = 0; sc < 3; sc++) {
    const w = boardSettledWinner(sr, sc);
    settled.push(w);
    if (w === 'X') xSettled++;
    if (w === 'O') oSettled++;
  }
  if (xSettled < 5 && oSettled < 5) return false;
  const forbidden = xSettled >= 5 ? 'X' : 'O';
  let changed = false, idx = 0;
  for (let sr = 0; sr < 3; sr++) for (let sc = 0; sc < 3; sc++, idx++) {
    if (settled[idx]) continue;
    if (forceBoardCellsExcluding(sr, sc, [forbidden])) changed = true;
  }
  return changed;
}

// Rule: meta-line outcome exclusion. Mirrors ruleLineExhaustion one level
// up — the revealed overall winner (metaOutcome) means no super-line of 3
// boards can ever complete for the OTHER symbol(s). If 2 of a line's 3
// boards are already settled to a forbidden symbol, the 3rd can't be it
// either.
function ruleMetaLineOutcome() {
  if (!metaOutcome) return false;
  const forbiddenSymbols = metaOutcome === 'draw' ? ['X', 'O'] : (metaOutcome === 'X' ? ['O'] : ['X']);
  const settled = [];
  for (let sr = 0; sr < 3; sr++) for (let sc = 0; sc < 3; sc++) settled.push(boardSettledWinner(sr, sc));

  const exclusions = Array.from({ length: 9 }, () => new Set());
  for (const line of LINES) {
    for (const sym of forbiddenSymbols) {
      const settledCount = line.filter((i) => settled[i] === sym).length;
      const unsettledIdx = line.filter((i) => !settled[i]);
      if (settledCount === 2 && unsettledIdx.length === 1) exclusions[unsettledIdx[0]].add(sym);
    }
  }
  let changed = false, idx = 0;
  for (let sr = 0; sr < 3; sr++) for (let sc = 0; sc < 3; sc++, idx++) {
    if (settled[idx] || exclusions[idx].size === 0) continue;
    if (forceBoardCellsExcluding(sr, sc, [...exclusions[idx]])) changed = true;
  }
  return changed;
}

// A clued row/column already has more X's (or O's) placed than its target
// allows — used both by the chain-contradiction engine and by the live
// violation highlighting in render().
function lineExceedsClue(clue) {
  const curX = countLineSymbol(grid, clue.type, clue.index, 'X');
  const curO = countLineSymbol(grid, clue.type, clue.index, 'O');
  return curX > clue.targetX || curO > 9 - clue.targetX;
}

// Any board or line clue currently violated in the (possibly hypothetical)
// grid — used by the chain-contradiction engine below to detect dead ends.
function anyViolationNow() {
  for (let sr = 0; sr < 3; sr++) for (let sc = 0; sc < 3; sc++) if (boardViolation(sr, sc)) return true;
  for (const clue of lineClues) if (lineExceedsClue(clue)) return true;
  return false;
}

function findFirstEmpty() {
  for (let r = 0; r < 9; r++) for (let c = 0; c < 9; c++) if (!locked[r][c]) return [r, c];
  return null;
}

// Does the current state necessarily lead to a contradiction? First applies
// the cheap deterministic rules (1-3) to a fixpoint. If that's not enough
// and `depth` nested hypotheses remain, it tries both values for one empty
// cell and recurses — the state is only contradictory if BOTH branches are.
// depth=0 means "no nested hypothesis, deterministic rules only" (rule 4).
// depth=1/2/3 add one/two/three more nested levels (rules 5/6/7).
function stateContradicts(depth, budget) {
  let progress = true;
  while (progress) {
    progress = ruleMaxCapExhaustion() || ruleLineExhaustion() || ruleOutcomeLocal();
    if (anyViolationNow()) return true;
  }
  if (anyViolationNow()) return true;
  if (locked.every((row) => row.every((v) => v))) return false; // fully filled, consistent
  if (depth <= 0) return false; // can't go deeper — assume consistent (conservative)

  budget.calls++;
  if (budget.calls > budget.limit) { budget.aborted = true; return false; }

  const [r, c] = findFirstEmpty();
  const savedLocked = locked.map((row) => row.slice());
  const savedGrid = grid.map((row) => row.slice());

  grid[r][c] = 'X'; locked[r][c] = true;
  const xContra = stateContradicts(depth - 1, budget);
  locked = savedLocked.map((row) => row.slice());
  grid = savedGrid.map((row) => row.slice());
  if (budget.aborted) return false;

  grid[r][c] = 'O'; locked[r][c] = true;
  const oContra = stateContradicts(depth - 1, budget);
  locked = savedLocked.map((row) => row.slice());
  grid = savedGrid.map((row) => row.slice());
  if (budget.aborted) return false;

  return xContra && oContra;
}

// Rules 4-7: for each empty cell, hypothesize each value and see if it
// necessarily contradicts within `maxDepth` nested hypotheses. If only one
// value survives, it's forced. maxDepth 0/1/2/3 correspond to rules 4/5/6/7.
function ruleChainStep(maxDepth, budget) {
  let changed = false;
  for (let r = 0; r < 9; r++) {
    for (let c = 0; c < 9; c++) {
      if (locked[r][c]) continue;

      const savedLocked = locked.map((row) => row.slice());
      const savedGrid = grid.map((row) => row.slice());

      grid[r][c] = 'X'; locked[r][c] = true;
      const xContra = stateContradicts(maxDepth - 1, budget);
      locked = savedLocked.map((row) => row.slice());
      grid = savedGrid.map((row) => row.slice());
      if (budget.aborted) return { changed, aborted: true };

      grid[r][c] = 'O'; locked[r][c] = true;
      const oContra = stateContradicts(maxDepth - 1, budget);
      locked = savedLocked.map((row) => row.slice());
      grid = savedGrid.map((row) => row.slice());
      if (budget.aborted) return { changed, aborted: true };

      if (xContra && oContra) return { changed, aborted: true }; // shouldn't happen from a consistent state
      if (xContra) { grid[r][c] = 'O'; locked[r][c] = true; changed = true; }
      else if (oContra) { grid[r][c] = 'X'; locked[r][c] = true; changed = true; }
    }
  }
  return { changed, aborted: false };
}

// Generation ruleset (used by isDeductionSolvable/digHoles only — this is
// what determines which clues can be dug out). hard stops at chain1
// (nested-hypothesis depth 1, i.e. "hold ~2 tiles") — a numerical study
// found chain2/chain3 never fired once across 25 generated hard puzzles
// even when allowed, so they added nothing but generation cost. Capping
// here guarantees new puzzles never need deeper reasoning than that,
// instead of relying on it happening not to come up.
const RULESETS = {
  easy: ['split', 'line', 'outcomeLocal'],
  medium: ['split', 'line', 'outcomeLocal', 'chain0', 'chain1'],
  hard: ['split', 'line', 'outcomeLocal', 'chain0', 'chain1'],
};

// Hint/solvability-check ruleset (used by findHintArea only — never by
// digHoles/generation, deliberately, so these rules don't change what gets
// dug out). Adds metaCap and metaLine ahead of everything else, per the
// same study: they're each useful in a meaningful minority of puzzles
// (metaLine especially — up to 40% at hard) without ever dominating a
// solve. hard's hint ruleset keeps chain2/chain3 as a tail, purely so the
// Hint button still finds a deduction on any hard daily puzzle that was
// already in progress before the RULESETS.hard trim above — new puzzles
// should never actually need them, but this keeps existing saves working.
const HINT_RULESETS = {
  easy: ['metaCap', 'metaLine', ...RULESETS.easy],
  medium: ['metaCap', 'metaLine', ...RULESETS.medium],
  hard: ['metaCap', 'metaLine', ...RULESETS.hard, 'chain2', 'chain3'],
};

// A puzzle is deduction-solvable at a given tier if repeatedly applying only
// that tier's rules (cheapest first, restarting after any progress) reaches
// a full grid — never picking between two still-live possibilities.
function isDeductionSolvable(tier) {
  const rules = RULESETS[tier] || RULESETS.hard;
  const savedLocked = locked, savedGrid = grid;
  locked = locked.map((row) => row.slice());
  grid = grid.map((row) => row.slice());

  const budget = { calls: 0, limit: 1500, aborted: false };
  let progress = true;

  while (progress && !budget.aborted) {
    progress = false;
    for (const rule of rules) {
      let madeProgress = false;
      if (rule === 'split') madeProgress = ruleMaxCapExhaustion();
      else if (rule === 'line') madeProgress = ruleLineExhaustion();
      else if (rule === 'outcomeLocal') madeProgress = ruleOutcomeLocal();
      else if (rule === 'chain0') { const res = ruleChainStep(0, budget); madeProgress = res.changed; }
      else if (rule === 'chain1') { const res = ruleChainStep(1, budget); madeProgress = res.changed; }
      else if (rule === 'chain2') { const res = ruleChainStep(2, budget); madeProgress = res.changed; }
      else if (rule === 'chain3') { const res = ruleChainStep(3, budget); madeProgress = res.changed; }
      if (madeProgress) { progress = true; break; } // restart from the cheapest rule
      if (budget.aborted) break;
    }
  }

  const solved = !budget.aborted && locked.every((row) => row.every((v) => v));
  locked = savedLocked;
  grid = savedGrid;
  return solved;
}

// ---------- hint areas (read-only scans: locate a deduction, never apply it) ----------
// A board already at its 5-of-one-symbol cap -> the whole board is the
// relevant area (every empty cell in it is forced).
function scanSplitHint() {
  for (let sr = 0; sr < 3; sr++) {
    for (let sc = 0; sc < 3; sc++) {
      const { x, o } = boardSymbolCounts(sr, sc);
      if (x !== 5 && o !== 5) continue;
      for (let r = 0; r < 3; r++) {
        for (let c = 0; c < 3; c++) {
          const gr = sr * 3 + r, gc = sc * 3 + c;
          if (!locked[gr][gc]) return { type: 'board', sr, sc };
        }
      }
    }
  }
  return null;
}

// A clued row/column already has its full quota of one symbol placed -> that
// whole row/column is the relevant area.
function scanLineHint() {
  for (const clue of lineClues) {
    const targetO = 9 - clue.targetX;
    const curX = countLineSymbol(grid, clue.type, clue.index, 'X');
    const curO = countLineSymbol(grid, clue.type, clue.index, 'O');
    if (curX !== clue.targetX && curO !== targetO) continue;
    for (const [r, c] of lineCellCoords(clue.type, clue.index)) {
      if (!locked[r][c]) return { type: clue.type, index: clue.index };
    }
  }
  return null;
}

// A board with a known outcome whose local candidates all agree on some
// still-empty cell -> that board is the relevant area.
function scanOutcomeLocalHint() {
  for (let sr = 0; sr < 3; sr++) {
    for (let sc = 0; sc < 3; sc++) {
      if (!boardOutcomeClue[sr][sc]) continue;
      const cands = buildBoardCandidates(sr, sc);
      if (cands.length === 0) continue;
      for (let i = 0; i < 9; i++) {
        const gr = sr * 3 + Math.floor(i / 3), gc = sc * 3 + (i % 3);
        if (locked[gr][gc]) continue;
        const firstVal = cands[0].cells[i];
        if (cands.every((cand) => cand.cells[i] === firstVal)) return { type: 'board', sr, sc };
      }
    }
  }
  return null;
}

// A board not yet settled, but excluded from one symbol by the meta-cap
// rule (5 boards already settled to it), whose narrowed local candidates
// agree on some still-empty cell -> that board is the relevant area.
function scanMetaCapHint() {
  let xSettled = 0, oSettled = 0;
  const settled = [];
  for (let sr = 0; sr < 3; sr++) for (let sc = 0; sc < 3; sc++) {
    const w = boardSettledWinner(sr, sc);
    settled.push(w);
    if (w === 'X') xSettled++;
    if (w === 'O') oSettled++;
  }
  if (xSettled < 5 && oSettled < 5) return null;
  const forbidden = xSettled >= 5 ? 'X' : 'O';
  let idx = 0;
  for (let sr = 0; sr < 3; sr++) {
    for (let sc = 0; sc < 3; sc++, idx++) {
      if (settled[idx]) continue;
      const cands = buildBoardCandidatesExcluding(sr, sc, [forbidden]);
      if (cands.length === 0) continue;
      for (let i = 0; i < 9; i++) {
        const gr = sr * 3 + Math.floor(i / 3), gc = sc * 3 + (i % 3);
        if (locked[gr][gc]) continue;
        const firstVal = cands[0].cells[i];
        if (cands.every((cand) => cand.cells[i] === firstVal)) return { type: 'board', sr, sc };
      }
    }
  }
  return null;
}

// A board not yet settled, but excluded from a symbol by the meta-line
// rule (2 of its super-line's 3 boards already settled to a losing
// symbol), whose narrowed local candidates agree on some still-empty cell
// -> that board is the relevant area.
function scanMetaLineHint() {
  if (!metaOutcome) return null;
  const forbiddenSymbols = metaOutcome === 'draw' ? ['X', 'O'] : (metaOutcome === 'X' ? ['O'] : ['X']);
  const settled = [];
  for (let sr = 0; sr < 3; sr++) for (let sc = 0; sc < 3; sc++) settled.push(boardSettledWinner(sr, sc));

  const exclusions = Array.from({ length: 9 }, () => new Set());
  for (const line of LINES) {
    for (const sym of forbiddenSymbols) {
      const settledCount = line.filter((i) => settled[i] === sym).length;
      const unsettledIdx = line.filter((i) => !settled[i]);
      if (settledCount === 2 && unsettledIdx.length === 1) exclusions[unsettledIdx[0]].add(sym);
    }
  }
  let idx = 0;
  for (let sr = 0; sr < 3; sr++) {
    for (let sc = 0; sc < 3; sc++, idx++) {
      if (settled[idx] || exclusions[idx].size === 0) continue;
      const cands = buildBoardCandidatesExcluding(sr, sc, [...exclusions[idx]]);
      if (cands.length === 0) continue;
      for (let i = 0; i < 9; i++) {
        const gr = sr * 3 + Math.floor(i / 3), gc = sc * 3 + (i % 3);
        if (locked[gr][gc]) continue;
        const firstVal = cands[0].cells[i];
        if (cands.every((cand) => cand.cells[i] === firstVal)) return { type: 'board', sr, sc };
      }
    }
  }
  return null;
}

// Deeper chain-hypothesis deduction (rules 4-7): find the first empty cell
// where one value necessarily contradicts, without ever committing that
// value to the real grid. The board containing that cell is the area shown.
function scanChainHint(maxDepth, budget) {
  for (let r = 0; r < 9; r++) {
    for (let c = 0; c < 9; c++) {
      if (locked[r][c]) continue;

      const savedLocked = locked.map((row) => row.slice());
      const savedGrid = grid.map((row) => row.slice());

      grid[r][c] = 'X'; locked[r][c] = true;
      const xContra = stateContradicts(maxDepth - 1, budget);
      locked = savedLocked.map((row) => row.slice());
      grid = savedGrid.map((row) => row.slice());
      if (budget.aborted) return null;

      grid[r][c] = 'O'; locked[r][c] = true;
      const oContra = stateContradicts(maxDepth - 1, budget);
      locked = savedLocked.map((row) => row.slice());
      grid = savedGrid.map((row) => row.slice());
      if (budget.aborted) return null;

      if (xContra && oContra) return null; // shouldn't happen from a consistent state
      if (xContra || oContra) return { type: 'board', sr: Math.floor(r / 3), sc: Math.floor(c / 3) };
    }
  }
  return null;
}

// Finds the area (board, row, or column) containing a deduction reachable
// from the CURRENT board (including whatever the player has filled in so
// far, not just the original clues), using the same rules the active
// difficulty allows. Never fills in a cell — just points at where to look.
function findHintArea(tier) {
  const rules = HINT_RULESETS[tier] || HINT_RULESETS.hard;
  const savedLocked = locked, savedGrid = grid;
  // Treat every currently-filled cell (given clue or player entry) as known.
  locked = grid.map((row) => row.map((v) => v !== ''));
  grid = grid.map((row) => row.slice());

  const budget = { calls: 0, limit: 1500, aborted: false };
  let area = null;

  for (const rule of rules) {
    if (rule === 'metaCap') area = scanMetaCapHint();
    else if (rule === 'metaLine') area = scanMetaLineHint();
    else if (rule === 'split') area = scanSplitHint();
    else if (rule === 'line') area = scanLineHint();
    else if (rule === 'outcomeLocal') area = scanOutcomeLocalHint();
    else if (rule === 'chain0') area = scanChainHint(0, budget);
    else if (rule === 'chain1') area = scanChainHint(1, budget);
    else if (rule === 'chain2') area = scanChainHint(2, budget);
    else if (rule === 'chain3') area = scanChainHint(3, budget);
    if (area) break;
  }

  locked = savedLocked;
  grid = savedGrid;
  return area;
}

function areaCells(area) {
  const cells = [];
  if (area.type === 'board') {
    for (let r = 0; r < 3; r++) for (let c = 0; c < 3; c++) cells.push([area.sr * 3 + r, area.sc * 3 + c]);
  } else if (area.type === 'row') {
    for (let c = 0; c < 9; c++) cells.push([area.index, c]);
  } else if (area.type === 'col') {
    for (let r = 0; r < 9; r++) cells.push([r, area.index]);
  }
  return cells;
}

// Flashes the given cells with a fading highlight (~3s) so the player knows
// where a deduction is available, without picking the cell for them.
function flashCells(cells) {
  for (const el of cells) el.classList.remove('hintFlash');
  void document.body.offsetWidth; // force reflow so the animation restarts
  for (const el of cells) {
    el.classList.add('hintFlash');
    el.addEventListener('animationend', () => el.classList.remove('hintFlash'), { once: true });
  }
}

// ---------- full puzzle generation ----------
// Difficulty works three ways: which rules are allowed (RULESETS above), how
// many board-outcome badges are guaranteed to survive (picked up front, see
// pickProtectedOutcomes), and soft floors on how few line clues / cells
// we'll strip down to even if the ruleset could go further (see digHoles
// for why lines and cells are dug from one interleaved pool rather than
// lines-to-floor-first).
const DIFFICULTY_OUTCOME_RANGE = { easy: [6, 8], medium: [4, 7], hard: [3, 5] };
const DIFFICULTY_MIN_LINES = { easy: 2, medium: 2, hard: 4 };
const DIFFICULTY_MIN_CELLS = { easy: 22, medium: 16, hard: 14 };

function buildFullClueState() {
  locked = Array.from({ length: 9 }, () => Array(9).fill(true));
  grid = solution.map((row) => row.slice());
  boardOutcomeClue = [[null, null, null], [null, null, null], [null, null, null]];
  for (let sr = 0; sr < 3; sr++) {
    for (let sc = 0; sc < 3; sc++) boardOutcomeClue[sr][sc] = boardWinner(getBoardCells(solution, sr, sc));
  }
  lineClues = [];
  for (let i = 0; i < 9; i++) {
    lineClues.push({ type: 'row', index: i, targetX: countLineX(solution, 'row', i) });
    lineClues.push({ type: 'col', index: i, targetX: countLineX(solution, 'col', i) });
  }
}

// Picks how many board-outcome badges this puzzle keeps (drawn from the
// difficulty's target range) and which boards they are, then immediately
// clears the rest. Always safe to do outright — every cell is still locked
// at this point, so the puzzle is trivially solvable regardless of which
// outcome badges are present. Returns the kept boards as a "sr,sc" set so
// digHoles knows never to touch them.
function pickProtectedOutcomes(range) {
  const [lo, hi] = range;
  const target = lo + Math.floor(rng() * (hi - lo + 1));
  const coords = [];
  for (let sr = 0; sr < 3; sr++) for (let sc = 0; sc < 3; sc++) coords.push([sr, sc]);
  shuffle(coords);
  const kept = coords.slice(0, target);
  for (const [sr, sc] of coords.slice(target)) boardOutcomeClue[sr][sc] = null;
  return new Set(kept.map(([sr, sc]) => `${sr},${sc}`));
}

function allLineItems() {
  const items = [];
  for (let i = 0; i < 9; i++) {
    items.push({ kind: 'line', type: 'row', index: i });
    items.push({ kind: 'line', type: 'col', index: i });
  }
  return items;
}

function allCellItems() {
  const items = [];
  for (let r = 0; r < 9; r++) for (let c = 0; c < 9; c++) items.push({ kind: 'cell', r, c });
  return items;
}

function countLockedCells() {
  let n = 0;
  for (let r = 0; r < 9; r++) for (let c = 0; c < 9; c++) if (locked[r][c]) n++;
  return n;
}

// Removes one clue item, returning an undo function, or null if it was
// already absent.
function removeClueItem(item) {
  if (item.kind === 'cell') {
    if (!locked[item.r][item.c]) return null;
    const prevVal = grid[item.r][item.c];
    locked[item.r][item.c] = false;
    grid[item.r][item.c] = '';
    return () => { locked[item.r][item.c] = true; grid[item.r][item.c] = prevVal; };
  }
  const idx = lineClues.findIndex((cl) => cl.type === item.type && cl.index === item.index);
  if (idx === -1) return null;
  const removed = lineClues.splice(idx, 1)[0];
  return () => { lineClues.push(removed); };
}

// Repeatedly tries removing clues (lines and cells interleaved in one
// shuffled pool, same shape as the original single-pool dig) as long as the
// puzzle stays solvable by the tier's allowed rules, until a full pass
// removes nothing more or time runs out. Each item still respects its own
// type's floor. Lines are NOT dug to their floor as a separate first phase —
// that variant was tried and wiped lines out completely every time, which
// starved the solver of line-exhaustion deductions and forced far more
// cells to stay revealed to remain solvable, ballooning total clue count
// instead of just reshaping it. Interleaving lets the extra outcome info
// (see pickProtectedOutcomes) organically make some lines removable without
// blowing the puzzle's overall difficulty budget.
function digHoles(tier, minLines, minCells, startTime, timeBudgetMs) {
  const items = [...allLineItems(), ...allCellItems()];
  let progressed = true;
  while (progressed) {
    if (Date.now() - startTime > timeBudgetMs) break;
    progressed = false;
    for (const item of shuffle(items.slice())) {
      if (Date.now() - startTime > timeBudgetMs) break;
      if (item.kind === 'line' && lineClues.length <= minLines) continue;
      if (item.kind === 'cell' && countLockedCells() <= minCells) continue;
      const undo = removeClueItem(item);
      if (!undo) continue;
      if (isDeductionSolvable(tier)) progressed = true;
      else undo();
    }
  }
}

function generatePuzzle(difficulty) {
  const tier = RULESETS[difficulty] ? difficulty : 'medium';
  const outcomeRange = DIFFICULTY_OUTCOME_RANGE[tier] ?? DIFFICULTY_OUTCOME_RANGE.medium;
  const minLines = DIFFICULTY_MIN_LINES[tier] ?? DIFFICULTY_MIN_LINES.medium;
  const minCells = DIFFICULTY_MIN_CELLS[tier] ?? DIFFICULTY_MIN_CELLS.medium;
  const startTime = Date.now();

  solution = generateRandomSolution();
  metaOutcome = metaWinner(solution); // guaranteed non-void by generateRandomSolution
  metaMessage = pickMetaMessage(metaOutcome);
  candidateCache = new Map();
  moveHistory = [];
  redoStack = [];
  resetViolationState();
  celebrationToken++;
  celebrating = false;
  wonAlready = false;

  buildFullClueState();
  pickProtectedOutcomes(outcomeRange);
  digHoles(tier, minLines, minCells, startTime, GEN_TIME_BUDGET_MS);

  // isDeductionSolvable only ever forces a value when it's the sole option
  // consistent with a valid solution, so digHoles finishing already proves
  // this puzzle is uniquely solvable — no separate uniqueness search needed.
  return true;
}

// ---------- daily puzzles & persistence ----------
// Pacific time (auto-adjusts for PST/PDT) so the daily puzzle rolls over at
// midnight in that zone regardless of the visitor's own time zone.
function todayPacificString() {
  const parts = new Intl.DateTimeFormat('en-CA', {
    timeZone: 'America/Los_Angeles',
    year: 'numeric', month: '2-digit', day: '2-digit',
  }).formatToParts(new Date());
  const lookup = Object.fromEntries(parts.map((p) => [p.type, p.value]));
  return `${lookup.year}-${lookup.month}-${lookup.day}`;
}

function dailyStorageKey(dateStr, difficulty) {
  return `ttt-daily-${dateStr}-${difficulty}`;
}

const SAVE_PREF_KEY = 'ttt-save-enabled';
function isSavingEnabled() {
  try {
    const v = localStorage.getItem(SAVE_PREF_KEY);
    return v === null ? true : v === 'true'; // default on until the user opts out
  } catch (e) {
    return false; // localStorage unavailable — nothing to save anyway
  }
}
function setSavingEnabled(enabled) {
  try { localStorage.setItem(SAVE_PREF_KEY, enabled ? 'true' : 'false'); } catch (e) { /* ignore */ }
}

function saveDailyProgress() {
  if (!isDailyMode || !isSavingEnabled()) return;
  const key = dailyStorageKey(todayPacificString(), currentDifficulty);
  const data = { locked, grid, boardOutcomeClue, lineClues, metaOutcome, metaMessage };
  try { localStorage.setItem(key, JSON.stringify(data)); } catch (e) { /* storage unavailable or full — ignore */ }
}

function loadDailyProgress(dateStr, difficulty) {
  try {
    const raw = localStorage.getItem(dailyStorageKey(dateStr, difficulty));
    return raw ? JSON.parse(raw) : null;
  } catch (e) {
    return null;
  }
}

// A saved puzzle is "solved" if it's fully filled with no violations and
// every line clue satisfied — same condition render() checks live.
function isStateSolved(state) {
  const { locked: l, grid: g, boardOutcomeClue: boc, lineClues: lc } = state;
  const filled = g.every((row) => row.every((v) => v !== ''));
  if (!filled) return false;
  for (let sr = 0; sr < 3; sr++) {
    for (let sc = 0; sc < 3; sc++) {
      let x = 0, o = 0;
      for (let r = 0; r < 3; r++) for (let c = 0; c < 3; c++) {
        const v = g[sr * 3 + r][sc * 3 + c];
        if (v === 'X') x++; if (v === 'O') o++;
      }
      if (x > 5 || o > 5) return false;
      const cells = [];
      for (let r = 0; r < 3; r++) for (let c = 0; c < 3; c++) cells.push(g[sr * 3 + r][sc * 3 + c]);
      const winner = boardWinner(cells);
      if (winner === 'void') return false;
      const clue = boc[sr][sc];
      if (clue && winner !== clue) return false;
    }
  }
  for (const clue of lc) {
    if (countLineSymbol(g, clue.type, clue.index, 'X') !== clue.targetX) return false;
  }
  return true;
}

function dailyStatus(dateStr, difficulty) {
  const state = loadDailyProgress(dateStr, difficulty);
  if (!state) return 'new';
  return isStateSolved(state) ? 'solved' : 'inprogress';
}

// Generates today's puzzle for a difficulty deterministically — every
// visitor's browser runs the same generator with the same seed and lands
// on the exact same puzzle.
function generateDailyPuzzle(dateStr, difficulty) {
  rng = makeSeededRng(`supertictactoe-${dateStr}-${difficulty}`);
  const ok = generatePuzzle(difficulty);
  rng = Math.random;
  return ok;
}

function restoreState(state) {
  locked = state.locked;
  grid = state.grid;
  boardOutcomeClue = state.boardOutcomeClue;
  lineClues = state.lineClues;
  metaOutcome = state.metaOutcome || null; // older saves predate this field
  // Saves from before per-message variety (metaOutcome but no metaMessage
  // yet) get a message picked now instead of staying blank.
  metaMessage = state.metaMessage || (metaOutcome ? pickMetaMessage(metaOutcome) : null);
  candidateCache = new Map();
  moveHistory = [];
  redoStack = [];
  resetViolationState();
  celebrationToken++;
  celebrating = false;
  wonAlready = isStateSolved(state); // don't replay the celebration for an already-solved puzzle
}


function boardSymbolCounts(sr, sc) {
  let x = 0, o = 0;
  for (let r = 0; r < 3; r++) {
    for (let c = 0; c < 3; c++) {
      const v = grid[sr * 3 + r][sc * 3 + c];
      if (v === 'X') x++;
      if (v === 'O') o++;
    }
  }
  return { x, o };
}

function boardViolation(sr, sc) {
  const { x, o } = boardSymbolCounts(sr, sc);
  if (x > 5 || o > 5) return true;
  const winner = boardWinner(getBoardCells(grid, sr, sc));
  if (winner === 'void') return true;
  const clue = boardOutcomeClue[sr][sc];
  if (clue) {
    const filled = boardSymbolCounts(sr, sc).x + boardSymbolCounts(sr, sc).o === 9;
    if (winner !== 'draw' && winner !== clue) return true; // wrong line already completed
    if (filled && winner !== clue) return true; // filled but landed on the wrong outcome
  }
  return false;
}

function currentLineX(type, index) {
  return countLineX(grid, type, index);
}

// ---------- UI ----------
function resetGrid() {
  celebrationToken++;
  celebrating = false;
  wonAlready = false;
  moveHistory = [];
  redoStack = [];
  resetViolationState();
  for (let r = 0; r < 9; r++) for (let c = 0; c < 9; c++) if (!locked[r][c]) grid[r][c] = '';
  render();
}

function undoMove() {
  if (celebrating) return;
  const last = moveHistory.pop();
  if (!last) return;
  grid[last.r][last.c] = last.prevVal;
  redoStack.push(last);
  render();
}

function redoMove() {
  if (celebrating) return;
  const next = redoStack.pop();
  if (!next) return;
  grid[next.r][next.c] = next.newVal;
  moveHistory.push(next);
  render();
}

function showGameScreen() {
  document.getElementById('menuScreen').classList.add('hidden');
  document.getElementById('gameScreen').classList.remove('hidden');
  document.getElementById('dailyLabel').classList.toggle('hidden', !isDailyMode);
  document.getElementById('difficultyButtons').classList.toggle('hidden', isDailyMode);
  for (const btn of document.querySelectorAll('.diffBtn')) {
    btn.classList.toggle('active', btn.dataset.difficulty === currentDifficulty);
  }
  if (isDailyMode) {
    document.getElementById('dailyLabel').textContent =
      `Daily (${todayPacificString()}) — ${currentDifficulty[0].toUpperCase()}${currentDifficulty.slice(1)}`;
  }
}

function showMenu() {
  document.getElementById('gameScreen').classList.add('hidden');
  document.getElementById('menuScreen').classList.remove('hidden');
  const today = todayPacificString();
  document.getElementById('todayLabel').textContent = `Today: ${today} (Pacific)`;
  for (const card of document.querySelectorAll('.dailyCard')) {
    const difficulty = card.dataset.difficulty;
    const status = dailyStatus(today, difficulty);
    const label = status === 'solved' ? 'Solved ✓' : status === 'inprogress' ? 'In progress' : 'Not started';
    card.querySelector('.cardStatus').textContent = label;
    card.querySelector('.cardStatus').className = `cardStatus ${status}`;
  }
}

function startDaily(difficulty) {
  isDailyMode = true;
  currentDifficulty = difficulty;
  const today = todayPacificString();
  const saved = loadDailyProgress(today, difficulty);
  if (saved) {
    restoreState(saved);
    showGameScreen();
    render();
    return;
  }
  document.getElementById('status').textContent = 'Generating today\u2019s puzzle…';
  showGameScreen();
  setTimeout(() => {
    const ok = generateDailyPuzzle(today, difficulty);
    if (!ok) document.getElementById('status').textContent = "Couldn't confirm this one is solvable by pure deduction within the time budget — playable, but may need a guess somewhere.";
    render();
  }, 10);
}

function startPractice(difficulty) {
  isDailyMode = false;
  rng = Math.random;
  currentDifficulty = difficulty;
  document.getElementById('status').textContent = 'Generating puzzle…';
  showGameScreen();
  setTimeout(() => {
    const ok = generatePuzzle(currentDifficulty);
    if (!ok) document.getElementById('status').textContent = "Couldn't confirm this one is solvable by pure deduction within the time budget — playable, but may need a guess somewhere.";
    render();
  }, 10);
}

// Same debounce shape as the board-violation highlight above: only shows
// once a row/column's clue has been over its X or O target for a full
// second, so cycling a cell through blank->X->O doesn't flash red on a
// momentary overshoot.
function updateLineViolationTracking(type, index, isViolating) {
  const displayed = type === 'row' ? displayedRowViolations : displayedColViolations;
  const timers = type === 'row' ? pendingRowViolationTimers : pendingColViolationTimers;
  if (isViolating) {
    if (!displayed[index] && !timers[index]) {
      timers[index] = setTimeout(() => {
        timers[index] = null;
        const clue = lineClues.find((cl) => cl.type === type && cl.index === index);
        if (clue && lineExceedsClue(clue)) {
          displayed[index] = true;
          render();
        }
      }, 1000);
    }
  } else {
    displayed[index] = false;
    if (timers[index]) {
      clearTimeout(timers[index]);
      timers[index] = null;
    }
  }
}

function render() {
  const CELL = 58;
  const EDGE = 70;
  const GAP = 3;
  const MARGIN = 8;

  const wrap = document.getElementById('boardWrap');
  wrap.innerHTML = '';
  wrap.style.display = 'flex';
  wrap.style.flexDirection = 'column';

  cellElements = Array.from({ length: 9 }, () => Array(9).fill(null));
  edgeBoxes = { colBlue: {}, rowBlue: {}, rowRed: {}, colRed: {} };

  const violations = [[false, false, false], [false, false, false], [false, false, false]];
  for (let sr = 0; sr < 3; sr++) for (let sc = 0; sc < 3; sc++) violations[sr][sc] = boardViolation(sr, sc);

  // Debounce the red violation highlight: cycling a cell through blank->X->O
  // often passes through a momentarily-invalid X before landing on a valid O,
  // so only show the highlight once a violation has held steady for 1s.
  for (let sr = 0; sr < 3; sr++) {
    for (let sc = 0; sc < 3; sc++) {
      if (violations[sr][sc]) {
        if (!displayedViolations[sr][sc] && !pendingViolationTimers[sr][sc]) {
          pendingViolationTimers[sr][sc] = setTimeout(() => {
            pendingViolationTimers[sr][sc] = null;
            if (boardViolation(sr, sc)) {
              displayedViolations[sr][sc] = true;
              render();
            }
          }, 1000);
        }
      } else {
        displayedViolations[sr][sc] = false;
        if (pendingViolationTimers[sr][sc]) {
          clearTimeout(pendingViolationTimers[sr][sc]);
          pendingViolationTimers[sr][sc] = null;
        }
      }
    }
  }

  // Same idea, one level up: a clued row/column with more X's or O's placed
  // than its target allows. Lines without a clue (dug out as part of
  // difficulty) have nothing to violate against.
  for (let i = 0; i < 9; i++) {
    const rowClue = lineClues.find((cl) => cl.type === 'row' && cl.index === i);
    updateLineViolationTracking('row', i, rowClue ? lineExceedsClue(rowClue) : false);
    const colClue = lineClues.find((cl) => cl.type === 'col' && cl.index === i);
    updateLineViolationTracking('col', i, colClue ? lineExceedsClue(colClue) : false);
  }

  const topOuter = document.createElement('div');
  topOuter.style.display = 'flex';
  const topSpacer = document.createElement('div');
  topSpacer.style.width = `${EDGE}px`;
  topOuter.appendChild(topSpacer);
  const topRow = document.createElement('div');
  topRow.style.display = 'grid';
  topRow.style.gridTemplateColumns = `repeat(9, ${CELL}px)`;
  topRow.style.gap = `${GAP}px`;
  topRow.style.marginBottom = `${MARGIN}px`;
  for (let c = 0; c < 9; c++) {
    const box = document.createElement('div');
    box.style.height = `${CELL}px`;
    box.style.display = 'flex';
    box.style.alignItems = 'center';
    box.style.justifyContent = 'center';
    box.style.position = 'relative';
    const clue = lineClues.find((cl) => cl.type === 'col' && cl.index === c);
    if (clue) {
      const targetO = 9 - clue.targetX;
      const curO = countLineSymbol(grid, 'col', c, 'O');
      const oClass = curO === targetO ? 'clueNumBig o-done' : 'clueNumBig o-active';
      box.title = `Column ${c + 1}: needs ${targetO} O's`;
      box.innerHTML = `<span class="${oClass}">${targetO}</span>`;
      edgeBoxes.colBlue[c] = box;
    }
    topRow.appendChild(box);
  }
  topOuter.appendChild(topRow);
  wrap.appendChild(topOuter);

  const mainRow = document.createElement('div');
  mainRow.style.display = 'flex';

  const leftCol = document.createElement('div');
  leftCol.style.display = 'grid';
  leftCol.style.gridTemplateRows = `repeat(9, ${CELL}px)`;
  leftCol.style.gap = `${GAP}px`;
  leftCol.style.marginRight = `${MARGIN}px`;
  for (let r = 0; r < 9; r++) {
    const box = document.createElement('div');
    box.style.width = `${EDGE}px`;
    box.style.display = 'flex';
    box.style.alignItems = 'center';
    box.style.justifyContent = 'center';
    box.style.position = 'relative';
    const clue = lineClues.find((cl) => cl.type === 'row' && cl.index === r);
    if (clue) {
      const targetO = 9 - clue.targetX;
      const curO = countLineSymbol(grid, 'row', r, 'O');
      const oClass = curO === targetO ? 'clueNumBig o-done' : 'clueNumBig o-active';
      box.title = `Row ${r + 1}: needs ${targetO} O's`;
      box.innerHTML = `<span class="${oClass}">${targetO}</span>`;
      edgeBoxes.rowBlue[r] = box;
    }
    leftCol.appendChild(box);
  }
  mainRow.appendChild(leftCol);

  const gridEl = document.createElement('div');
  gridEl.style.display = 'grid';
  gridEl.style.gridTemplateColumns = `repeat(9, ${CELL}px)`;
  gridEl.style.gridTemplateRows = `repeat(9, ${CELL}px)`;
  gridEl.style.gap = `${GAP}px`;

  for (let r = 0; r < 9; r++) {
    for (let c = 0; c < 9; c++) {
      const sr = Math.floor(r / 3), sc = Math.floor(c / 3);
      const cellEl = document.createElement('div');
      cellEl.className = 'cell';
      if (locked[r][c]) cellEl.classList.add('locked');
      if (displayedViolations[sr][sc] || displayedRowViolations[r] || displayedColViolations[c]) cellEl.classList.add('violation');
      const outcomeClue = boardOutcomeClue[sr][sc];
      if (outcomeClue) cellEl.classList.add(`tint-${outcomeClue}`);
      const val = grid[r][c];
      if (val) cellEl.classList.add(val);
      cellEl.textContent = val;
      if (c % 3 === 2 && c !== 8) cellEl.classList.add('thickRight');
      if (r % 3 === 2 && r !== 8) cellEl.classList.add('thickBottom');
      if (!locked[r][c]) {
        cellEl.addEventListener('click', () => {
          if (celebrating) return;
          const v = grid[r][c];
          const newVal = v === '' ? 'X' : v === 'X' ? 'O' : '';
          moveHistory.push({ r, c, prevVal: v, newVal });
          redoStack = [];
          grid[r][c] = newVal;
          render();
        });
      }
      cellElements[r][c] = cellEl;
      if (r % 3 === 0 && c % 3 === 0 && outcomeClue) {
        const badge = document.createElement('span');
        badge.className = `cornerBadge ${outcomeClue}`;
        badge.textContent = outcomeClue === 'draw' ? '–' : outcomeClue;
        badge.title = 'Given: this board\u2019s winner';
        cellEl.appendChild(badge);
      }
      gridEl.appendChild(cellEl);
    }
  }
  mainRow.appendChild(gridEl);

  const rightCol = document.createElement('div');
  rightCol.style.display = 'grid';
  rightCol.style.gridTemplateRows = `repeat(9, ${CELL}px)`;
  rightCol.style.gap = `${GAP}px`;
  rightCol.style.marginLeft = `${MARGIN}px`;
  for (let r = 0; r < 9; r++) {
    const box = document.createElement('div');
    box.style.width = `${EDGE}px`;
    box.style.display = 'flex';
    box.style.alignItems = 'center';
    box.style.justifyContent = 'center';
    box.style.position = 'relative';
    const clue = lineClues.find((cl) => cl.type === 'row' && cl.index === r);
    if (clue) {
      const curX = countLineSymbol(grid, 'row', r, 'X');
      const xClass = curX === clue.targetX ? 'clueNumBig x-done' : 'clueNumBig x-active';
      box.title = `Row ${r + 1}: needs ${clue.targetX} X's`;
      box.innerHTML = `<span class="${xClass}">${clue.targetX}</span>`;
      edgeBoxes.rowRed[r] = box;
    }
    rightCol.appendChild(box);
  }
  mainRow.appendChild(rightCol);
  wrap.appendChild(mainRow);

  const bottomOuter = document.createElement('div');
  bottomOuter.style.display = 'flex';
  const bottomSpacer = document.createElement('div');
  bottomSpacer.style.width = `${EDGE}px`;
  bottomOuter.appendChild(bottomSpacer);
  const bottomRow = document.createElement('div');
  bottomRow.style.display = 'grid';
  bottomRow.style.gridTemplateColumns = `repeat(9, ${CELL}px)`;
  bottomRow.style.gap = `${GAP}px`;
  bottomRow.style.marginTop = `${MARGIN}px`;
  for (let c = 0; c < 9; c++) {
    const box = document.createElement('div');
    box.style.height = `${CELL}px`;
    box.style.display = 'flex';
    box.style.alignItems = 'center';
    box.style.justifyContent = 'center';
    box.style.textAlign = 'center';
    box.style.position = 'relative';
    const clue = lineClues.find((cl) => cl.type === 'col' && cl.index === c);
    if (clue) {
      const curX = countLineSymbol(grid, 'col', c, 'X');
      const xClass = curX === clue.targetX ? 'clueNumBig x-done' : 'clueNumBig x-active';
      box.title = `Column ${c + 1}: needs ${clue.targetX} X's`;
      box.innerHTML = `<span class="${xClass}">${clue.targetX}</span>`;
      edgeBoxes.colRed[c] = box;
    }
    bottomRow.appendChild(box);
  }
  bottomOuter.appendChild(bottomRow);
  wrap.appendChild(bottomOuter);

  const filled = grid.every((row) => row.every((v) => v !== ''));
  const noViolations = violations.every((row) => row.every((v) => !v));
  const lineClueOk = lineClues.every((cl) => currentLineX(cl.type, cl.index) === cl.targetX);
  const statusEl = document.getElementById('status');
  if (filled) {
    const solved = noViolations && lineClueOk;
    statusEl.textContent = solved
      ? 'Solved! Every constraint is satisfied.'
      : 'All cells filled, but something is still off — check the highlighted mismatches.';
    if (solved && !wonAlready) {
      wonAlready = true;
      const token = celebrationToken;
      setTimeout(() => { if (celebrationToken === token) playWinAnimation(token); }, 150);
    }
  } else {
    statusEl.textContent = '';
  }

  const metaEl = document.getElementById('metaResult');
  if (metaEl) {
    metaEl.textContent = metaMessage || '';
    metaEl.className = metaOutcome ? `metaResult-${metaOutcome}` : '';
  }

  saveDailyProgress();
  updateControlButtons();
}

function updateControlButtons() {
  document.getElementById('resetBtn').disabled = !hasPlayerProgress();
  document.getElementById('undoBtn').disabled = moveHistory.length === 0;
  document.getElementById('redoBtn').disabled = redoStack.length === 0;
}

// Blue squares sweep top-left -> bottom-right; the instant that wavefront
// reaches the far corner, red squares sweep bottom-right -> top-left (same
// diagonal family, opposite direction) — sharp-edged growing/shrinking
// squares, not blurred. Edge numbers glow (grey -> saturated -> white ->
// saturated -> grey) as their row/column is reached instead of getting a
// square. Finale: a radial wave from the board's center, both colors at
// once, that leaves each tile persistently highlighted in its own color.
function pulseElement(container, color, delayMs, durationMs) {
  if (!container) return;
  const sq = document.createElement('div');
  sq.className = `pulseSq pulseSq-${color}`;
  sq.style.animation = `pulseGrow ${durationMs}ms ease-in-out ${delayMs}ms 1 both`;
  container.appendChild(sq);
  setTimeout(() => { if (sq.parentNode) sq.parentNode.removeChild(sq); }, delayMs + durationMs + 60);
}

// Same growing square, but holds at full size instead of shrinking back —
// used for the radial finale so it leaves a highlighted trail behind it.
function pulseElementHold(container, color, delayMs, durationMs) {
  if (!container) return;
  const sq = document.createElement('div');
  sq.className = `pulseSq pulseSq-${color}-hold`;
  sq.style.animation = `growHold ${durationMs}ms ease-in-out ${delayMs}ms 1 both`;
  container.appendChild(sq);
}

function glowNumber(box, color, delayMs, durationMs) {
  if (!box) return;
  const span = box.querySelector('span');
  if (!span) return;
  const anim = color === 'blue' ? 'numberGlowBlue' : 'numberGlowRed';
  span.style.animation = `${anim} ${durationMs}ms ease-in-out ${delayMs}ms 1 both`;
}

function playWinAnimation(token) {
  celebrating = true;
  const STEP = 45, DUR = 380, TRAVEL = 16 * STEP;

  // Wave 1: blue, top-left -> bottom-right.
  for (let r = 0; r < 9; r++) {
    for (let c = 0; c < 9; c++) {
      if (grid[r][c] === 'O') pulseElement(cellElements[r][c], 'blue', (r + c) * STEP, DUR);
    }
  }
  for (let r = 0; r < 9; r++) glowNumber(edgeBoxes.rowBlue[r], 'blue', r * STEP, DUR);
  for (let c = 0; c < 9; c++) glowNumber(edgeBoxes.colBlue[c], 'blue', c * STEP, DUR);

  setTimeout(() => {
    if (celebrationToken !== token) return;

    // Wave 2: red, bottom-right -> top-left. Starts right as wave 1's front
    // lands on the far corner, no idle gap.
    for (let r = 0; r < 9; r++) {
      for (let c = 0; c < 9; c++) {
        if (grid[r][c] === 'X') pulseElement(cellElements[r][c], 'red', (16 - (r + c)) * STEP, DUR);
      }
    }
    for (let r = 0; r < 9; r++) glowNumber(edgeBoxes.rowRed[r], 'red', (8 - r) * STEP, DUR);
    for (let c = 0; c < 9; c++) glowNumber(edgeBoxes.colRed[c], 'red', (8 - c) * STEP, DUR);

    setTimeout(() => {
      if (celebrationToken !== token) return;

      // Finale: radial wave from center, both colors at once, leaves the
      // board persistently highlighted in its wake.
      const maxDist = Math.sqrt(32); // center (4,4) to a corner
      for (let r = 0; r < 9; r++) {
        for (let c = 0; c < 9; c++) {
          const dist = Math.sqrt((r - 4) ** 2 + (c - 4) ** 2);
          const delay = (dist / maxDist) * TRAVEL;
          const color = grid[r][c] === 'X' ? 'red' : 'blue';
          pulseElementHold(cellElements[r][c], color, delay, DUR);
        }
      }
      for (let r = 0; r < 9; r++) {
        const delay = (Math.abs(r - 4) / 4) * TRAVEL;
        glowNumber(edgeBoxes.rowBlue[r], 'blue', delay, DUR);
        glowNumber(edgeBoxes.rowRed[r], 'red', delay, DUR);
      }
      for (let c = 0; c < 9; c++) {
        const delay = (Math.abs(c - 4) / 4) * TRAVEL;
        glowNumber(edgeBoxes.colBlue[c], 'blue', delay, DUR);
        glowNumber(edgeBoxes.colRed[c], 'red', delay, DUR);
      }

      setTimeout(() => {
        if (celebrationToken === token) celebrating = false;
      }, TRAVEL + DUR);
    }, TRAVEL);
  }, TRAVEL);
}

function hasPlayerProgress() {
  for (let r = 0; r < 9; r++) {
    for (let c = 0; c < 9; c++) {
      if (!locked[r][c] && grid[r][c] !== '') return true;
    }
  }
  return false;
}

document.getElementById('resetBtn').addEventListener('click', resetGrid);
document.getElementById('undoBtn').addEventListener('click', undoMove);
document.getElementById('redoBtn').addEventListener('click', redoMove);

document.getElementById('hintBtn').addEventListener('click', () => {
  const area = findHintArea(currentDifficulty);
  if (!area) {
    document.getElementById('status').textContent = 'No forced move found from here — double check for mistakes, or try exploring another part of the board.';
    return;
  }
  const els = areaCells(area).map(([r, c]) => cellElements[r][c]).filter(Boolean);
  flashCells(els);
});

for (const btn of document.querySelectorAll('.diffBtn')) {
  btn.addEventListener('click', () => {
    const newDifficulty = btn.dataset.difficulty;
    if (hasPlayerProgress()) {
      const confirmed = window.confirm('Starting a new puzzle discards your current progress. Continue?');
      if (!confirmed) return;
    }
    startPractice(newDifficulty);
  });
}

document.getElementById('instructionsBtn').addEventListener('click', () => {
  document.getElementById('instructionsModal').classList.remove('hidden');
});
document.getElementById('closeInstructions').addEventListener('click', () => {
  document.getElementById('instructionsModal').classList.add('hidden');
});
document.getElementById('instructionsModal').addEventListener('click', (e) => {
  if (e.target.id === 'instructionsModal') e.target.classList.add('hidden');
});

document.getElementById('menuBtn').addEventListener('click', showMenu);
document.getElementById('freePlayBtn').addEventListener('click', () => startPractice('medium'));
for (const card of document.querySelectorAll('.dailyCard')) {
  card.addEventListener('click', () => startDaily(card.dataset.difficulty));
}

const saveToggle = document.getElementById('saveToggle');
saveToggle.checked = isSavingEnabled();
saveToggle.addEventListener('change', (e) => setSavingEnabled(e.target.checked));

showMenu();
