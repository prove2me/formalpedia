-- Prove2me | solution 1 for actuarial_c_weighted_survival_summation_by_parts
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:05:43.551193+00:00
-- url     : https://prove2.me/submissions/3f2cffad-2f22-4dfa-8778-6b8e92ef9e2d

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic




theorem solution
    (b f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), b j * (f j - f (j+1))) +
      b n * f (n+1) =
      b 0 * f 0 +
        ∑ j ∈ Finset.range n, (b (j+1) - b j) * f (j+1) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun j => (b (j+1) - b j) * f (j+1))]
    linear_combination ih

