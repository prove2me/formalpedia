-- Prove2me | solution 1 for WeilDefect.RPB108.physical_gap_of_denominator_bound
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T20:17:03.556235+00:00
-- url     : https://prove2.me/submissions/0908dea6-b95b-4336-9d11-cbe5a028b589

import Theorems.Thm_WeilDefect_RPB108_weighted_mass_sq_le_energy
import Mathlib
open scoped BigOperators
set_option autoImplicit false
open WeilDefect.RPB108
theorem solution {ι : Type*} (s : Finset ι)
    (w L : ι → ℝ) (hL : ∀ i ∈ s, 0 < L i) (gap : ℝ)
    (hgap : 0 ≤ gap)
    (hbound : gap * (∑ i ∈ s, (w i) ^ 2 / L i) ≤ 1)
    (z : ι → ℝ) :
    gap * (∑ i ∈ s, w i * |z i|) ^ 2 ≤ ∑ i ∈ s, L i * (z i) ^ 2 := by
  have he : 0 ≤ ∑ i ∈ s, L i * (z i) ^ 2 :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hL i hi).le (sq_nonneg _))
  calc
    gap * (∑ i ∈ s, w i * |z i|) ^ 2 ≤
        gap * ((∑ i ∈ s, (w i) ^ 2 / L i) *
          (∑ i ∈ s, L i * (z i) ^ 2)) :=
      mul_le_mul_of_nonneg_left (weighted_mass_sq_le_energy s w L z hL) hgap
    _ = (gap * (∑ i ∈ s, (w i) ^ 2 / L i)) *
        (∑ i ∈ s, L i * (z i) ^ 2) := by ring
    _ ≤ 1 * (∑ i ∈ s, L i * (z i) ^ 2) := mul_le_mul_of_nonneg_right hbound he
    _ = _ := one_mul _
