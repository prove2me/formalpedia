-- Prove2me | solution 1 for actuarial_c_actuarial_range_shift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T14:49:28.278422+00:00
-- url     : https://prove2.me/submissions/84b580d9-2dbd-4f38-8f14-5845a30322e5

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic



theorem solution (f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), f j) =
      f 0 + ∑ j ∈ Finset.range n, f (j+1) := by
  induction n with
  | zero => simp []
  | succ n ih => simp only [Finset.sum_range_succ] at *; linarith

