-- Prove2me | solution 1 for WeightedAverage.telescope_weighted
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T16:24:35.832081+00:00
-- url     : https://prove2.me/submissions/f18b488e-1f70-4dd2-9de5-a04eb4f0441d

import Mathlib

set_option autoImplicit false

-- carved from submission af8c70db-6fa0-4580-9851-54457c202aeb, lines 65-70

theorem solution (D : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * (D i - D (i + 1)) =
      ∑ i ∈ Finset.range n, D i - (n : ℝ) * D n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]; push_cast; ring
