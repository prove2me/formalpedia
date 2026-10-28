-- Prove2me | solution 1 for WeightedAverage.gauss_real
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T16:24:35.225991+00:00
-- url     : https://prove2.me/submissions/a2830da8-7f2d-4ae2-a24b-b8edfacd959a

import Mathlib

set_option autoImplicit false

-- carved from submission af8c70db-6fa0-4580-9851-54457c202aeb, lines 60-63

theorem solution (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i : ℝ) + 1) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
