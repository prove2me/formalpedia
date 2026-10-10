-- Prove2me | solution 1 for RhinViola.j1FiniteGeometricIdentity
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-10T05:22:26.549171+00:00
-- url     : https://prove2.me/submissions/27f39fd9-2f68-4141-ab61-3b2684560c20

import Mathlib.Tactic
open scoped BigOperators

theorem solution
    (a nu : ℕ) (x : ℝ) :
    x * Finset.sum (Finset.range nu) (fun i : ℕ => (1 - x) ^ (a + i)) =
      (1 - x) ^ a - (1 - x) ^ (a + nu) := by
  induction nu with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring
