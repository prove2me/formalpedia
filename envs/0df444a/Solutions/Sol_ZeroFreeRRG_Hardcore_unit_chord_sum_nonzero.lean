-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.unit_chord_sum_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:03:39.070103+00:00
-- url     : https://prove2.me/submissions/014538f6-a1b4-4541-910a-d45ece336263

import Theorems.Thm_ZeroFreeRRG_Hardcore_complex_sector_sum_nonzero
import Theorems.Thm_ZeroFreeRRG_Hardcore_unit_chord_projection
import Mathlib
set_option autoImplicit false
open ZeroFreeRRG.Hardcore
open scoped BigOperators

theorem solution {ι : Type} (S : Finset ι) (z : ι → ℂ) (u : ℂ)
    (hu : ‖u‖ = 1) (hS : S.Nonempty)
    (hn : ∀ i ∈ S, z i ≠ 0)
    (hclose : ∀ i ∈ S, ‖u-z i/(‖z i‖:ℂ)‖ ≤ 1/2) :
    ((7:ℝ)/8) * (∑ i ∈ S, ‖z i‖) ≤ ‖∑ i ∈ S, z i‖ ∧ (∑ i ∈ S, z i) ≠ 0 := by
  classical
  apply complex_sector_sum_nonzero S z u (7/8) hu (by norm_num)
  · intro i hi
    have hz : 0 < ‖z i‖ := norm_pos_iff.mpr (hn i hi)
    have hunit : ‖z i/(‖z i‖:ℂ)‖ = 1 := by
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz,div_self (ne_of_gt hz)]
    have hp := unit_chord_projection u (z i/(‖z i‖:ℂ)) hu hunit (hclose i hi)
    have hnco : (‖z i‖:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hz)
    have hid : z i = (z i/(‖z i‖:ℂ))*(‖z i‖:ℂ) := by field_simp
    have hre : (star u*z i).re = (star u*(z i/(‖z i‖:ℂ))).re * ‖z i‖ := by
      conv_lhs => rw [hid]
      simp [←mul_assoc,Complex.mul_re]
    rw [hre]
    exact mul_le_mul_of_nonneg_right hp hz.le
  · obtain ⟨i,hi⟩ := hS
    exact ⟨i,hi,hn i hi⟩
