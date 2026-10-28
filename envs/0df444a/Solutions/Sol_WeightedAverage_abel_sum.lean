-- Prove2me | solution 1 for WeightedAverage.abel_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T16:24:36.604839+00:00
-- url     : https://prove2.me/submissions/a7596fff-e9ab-4d98-a7ad-2a4caaf7f799

import Mathlib

set_option autoImplicit false

-- carved from submission af8c70db-6fa0-4580-9851-54457c202aeb, lines 49-58

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (z : ℕ → H) (zs : H) (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i : ℝ) + 1) • (z (i + 1) - z i) =
      (n : ℝ) • (z n - zs) - ∑ i ∈ Finset.range n, (z i - zs) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    push_cast
    module
