-- Prove2me | solution 1 for actuarial_c_slice_range_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:04:59.430153+00:00
-- url     : https://prove2.me/submissions/ad5ce2ad-01a0-46a1-9122-cdfb0c42c88a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals




theorem solution (h a n : ℕ) (f : ℕ → ℝ)
    (han : a+n ≤ h) :
    (∑ j ∈ Finset.range h, if a ≤ j ∧ j < a+n then f j else 0) =
       ∑ j ∈ Finset.range n, f (a+j) := by
  rw [← Finset.sum_filter]
  have : (Finset.range h).filter (fun j => a ≤ j ∧ j < a+n) = Finset.Ico a (a+n) := by
    ext j; simp [Finset.mem_Ico]; omega
  rw [this, Finset.sum_Ico_eq_sum_range]; simp

