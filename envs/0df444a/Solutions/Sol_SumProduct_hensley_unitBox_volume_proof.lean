-- Prove2me | solution 1 for SumProduct.hensley_unitBox_volume_proof
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:27:47.393326+00:00
-- url     : https://prove2.me/submissions/721952fd-51ab-4027-bd1a-a04508f24de6

import Definitions.Def_SumProduct_CubeSectionCore
import Definitions.Def_SumProduct_CubeSectionHensley
import Theorems.Thm_SumProduct_volume_cubeSection_fin_zero_toReal
import Theorems.Thm_SumProduct_card_index_eq
import Theorems.Thm_SumProduct_cubeSection_fin_one_volume_bounds
import Theorems.Thm_SumProduct_unitBox_eq_cubeSection
import Theorems.Thm_SumProduct_volume_cubeSection_one_congr
import Theorems.Thm_SumProduct_volume_cubeSection_toReal


set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
open scoped Classical
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
namespace SumProduct
theorem _root_.solution (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (r : ℝ) (hr : 0 ≤ r) :
    (2 * r) ^ (Module.finrank ℚ K - 1) / Real.sqrt (Module.finrank ℚ K)
        ≤ (volume (unitBox K r)).toReal ∧
      (volume (unitBox K r)).toReal
        ≤ 5 * (2 * r) ^ (Module.finrank ℚ K - 1) / Real.sqrt (Module.finrank ℚ K) := by
  classical
  have hd1 : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
  set m : ℕ := Module.finrank ℚ K - 1 with hm
  have hrm : (0 : ℝ) ≤ r ^ m := pow_nonneg hr _
  -- reduce the box volume to the unit `Fin m` cube section.
  have hbox : (volume (unitBox K r)).toReal
      = r ^ m * (volume (cubeSection (Fin m) 1)).toReal := by
    rw [unitBox_eq_cubeSection K r, volume_cubeSection_toReal r hr,
      volume_cubeSection_one_congr, card_index_eq (rfl : Module.finrank ℚ K = _)]
  rw [hbox]
  rcases eq_or_lt_of_le hd1 with hdeq | hd2
  · -- `d = 1`: `m = 0`, the cube section is a point of volume `1`; bounds are `1 ≤ 1 ≤ 5`.
    have hm0 : m = 0 := by omega
    rw [hm0, volume_cubeSection_fin_zero_toReal, ← hdeq]
    norm_num
  · -- `d ≥ 2`: apply the analytic core with `n = m ≥ 1`.
    have hmpos : 1 ≤ m := by omega
    obtain ⟨hlo, hhi⟩ := cubeSection_fin_one_volume_bounds m hmpos
    have hcast : ((m : ℝ) + 1) = (Module.finrank ℚ K : ℝ) := by
      have : (1 : ℕ) ≤ Module.finrank ℚ K := hd1
      rw [hm, Nat.cast_sub this]; ring
    rw [hcast] at hlo hhi
    set V1 := (volume (cubeSection (Fin m) 1)).toReal with hV1
    refine ⟨?_, ?_⟩
    · calc (2 * r) ^ m / Real.sqrt (Module.finrank ℚ K)
          = r ^ m * (2 ^ m / Real.sqrt (Module.finrank ℚ K)) := by rw [mul_pow]; ring
        _ ≤ r ^ m * V1 := mul_le_mul_of_nonneg_left hlo hrm
    · calc r ^ m * V1
          ≤ r ^ m * (5 * 2 ^ m / Real.sqrt (Module.finrank ℚ K)) :=
            mul_le_mul_of_nonneg_left hhi hrm
        _ = 5 * (2 * r) ^ m / Real.sqrt (Module.finrank ℚ K) := by rw [mul_pow]; ring
end SumProduct
