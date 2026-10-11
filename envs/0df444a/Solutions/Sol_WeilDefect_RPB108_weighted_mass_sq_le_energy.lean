-- Prove2me | solution 1 for WeilDefect.RPB108.weighted_mass_sq_le_energy
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T20:16:56.125174+00:00
-- url     : https://prove2.me/submissions/ebc640cc-4901-41a6-8b3e-c8a8bdf4d437

import Mathlib
open scoped BigOperators
set_option autoImplicit false
theorem solution {ι : Type*} (s : Finset ι)
    (w L z : ι → ℝ) (hL : ∀ i ∈ s, 0 < L i) :
    (∑ i ∈ s, w i * |z i|) ^ 2 ≤
      (∑ i ∈ s, (w i) ^ 2 / L i) * (∑ i ∈ s, L i * (z i) ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun i hi => div_nonneg (sq_nonneg _) (hL i hi).le)
    (fun i hi => mul_nonneg (hL i hi).le (sq_nonneg _))
  intro i hi
  have hn : L i ≠ 0 := ne_of_gt (hL i hi)
  rw [mul_pow, sq_abs]
  exact le_of_eq (by field_simp)
