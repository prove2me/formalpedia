-- Prove2me | solution 2 for WeightedAverage.abel_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T16:25:56.536422+00:00
-- url     : https://prove2.me/submissions/c77d8bf8-7b6b-48cf-a494-f8507f2ed9d5

import Mathlib

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (z : ℕ → H) (zs : H) (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i : ℝ) + 1) • (z (i + 1) - z i) =
      (n : ℝ) • (z n - zs) - ∑ i ∈ Finset.range n, (z i - zs) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    push_cast
    simp only [smul_sub, add_smul, one_smul]
    abel
