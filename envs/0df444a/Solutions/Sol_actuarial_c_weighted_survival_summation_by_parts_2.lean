-- Prove2me | solution 2 for actuarial_c_weighted_survival_summation_by_parts
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:14:11.937409+00:00
-- url     : https://prove2.me/submissions/7963965c-b399-4830-8af5-17528640f077

import Mathlib
set_option autoImplicit false

theorem solution
    (b f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), b j * (f j - f (j+1))) +
      b n * f (n+1) =
      b 0 * f 0 +
        ∑ j ∈ Finset.range n, (b (j+1) - b j) * f (j+1) := by
  induction n with
  | zero => simp only [zero_add, Finset.sum_range_one, Finset.range_zero, Finset.sum_empty, add_zero]; ring
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun j => (b (j+1) - b j) * f (j+1)) k]
    linarith
