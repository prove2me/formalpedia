-- Prove2me | solution 1 for WeilDefect.RPB108.physical_gap_of_mass_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T20:17:10.961477+00:00
-- url     : https://prove2.me/submissions/4800f429-d5c5-4296-9421-2bce257e1456

import Theorems.Thm_WeilDefect_RPB108_physical_gap_of_denominator_bound
import Mathlib
open scoped BigOperators
set_option autoImplicit false
open WeilDefect.RPB108
theorem solution {ι : Type*} (s : Finset ι)
    (w L : ι → ℝ) (hL : ∀ i ∈ s, 0 < L i) (gap : ℝ)
    (hgap : 0 ≤ gap)
    (hbound : gap * (∑ i ∈ s, (w i) ^ 2 / L i) ≤ 1)
    (z : ι → ℝ) (mass : ℝ) (hmass : 0 ≤ mass)
    (hupper : mass ≤ ∑ i ∈ s, w i * |z i|) :
    gap * mass ^ 2 ≤ ∑ i ∈ s, L i * (z i) ^ 2 := by
  have hu : 0 ≤ ∑ i ∈ s, w i * |z i| := hmass.trans hupper
  have hs : mass ^ 2 ≤ (∑ i ∈ s, w i * |z i|) ^ 2 := by
    nlinarith
  exact (mul_le_mul_of_nonneg_left hs hgap).trans
    (physical_gap_of_denominator_bound s w L hL gap hgap hbound z)
