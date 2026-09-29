-- Prove2me | solution 1 for TateCurve.exists_zpow_mul_mem_annulus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/005bfe52-3f0f-59ca-ae6d-8fd88897d15d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_exists_zpow_mul_mem_annulus
open scoped NNReal

namespace TateCurve
variable {K : Type*} [NontriviallyNormedField K] {q u : K}

private theorem nnnorm_lt_one_iff_norm {x : K} : ‖x‖₊ < 1 ↔ ‖x‖ < 1 := by
  rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]

private theorem exists_zpow_mul_norm_Ioc (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hu0 : u ≠ 0) :
    ∃ n : ℤ, ‖q‖ < ‖q ^ n * u‖ ∧ ‖q ^ n * u‖ ≤ 1 := by
  have hq_pos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hu_pos : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
  have hq_ne : (‖q‖ : ℝ) ≠ 0 := ne_of_gt hq_pos
  have hy : (1 : ℝ) < ‖q‖⁻¹ := one_lt_inv_iff₀.mpr ⟨hq_pos, hq⟩
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hu_pos hy
  have hqk_pos : (0 : ℝ) < ‖q‖ ^ (n + 1 : ℤ) := zpow_pos hq_pos _

  have hcancel : ∀ m : ℤ, ‖q‖⁻¹ ^ m * ‖q‖ ^ m = 1 := fun m => by
    rw [← mul_zpow, inv_mul_cancel₀ hq_ne, one_zpow]
  refine ⟨n + 1, ?_, ?_⟩
  ·
    have hkey : ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ n = ‖q‖ := by
      rw [zpow_add₀ hq_ne, zpow_one]
      calc ‖q‖ ^ n * ‖q‖ * ‖q‖⁻¹ ^ n
          = ‖q‖⁻¹ ^ n * (‖q‖ ^ n * ‖q‖) := mul_comm _ _
        _ = ‖q‖⁻¹ ^ n * ‖q‖ ^ n * ‖q‖ := (mul_assoc _ _ _).symm
        _ = 1 * ‖q‖ := by rw [hcancel n]
        _ = ‖q‖ := one_mul _
    have hlt : ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ n < ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ :=
      mul_lt_mul_of_pos_left hn1 hqk_pos
    rw [norm_mul, norm_zpow]
    calc ‖q‖ = ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ n := hkey.symm
      _ < ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ := hlt
  ·
    have hkey : ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1) = 1 := by
      calc ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1)
          = ‖q‖⁻¹ ^ (n + 1) * ‖q‖ ^ (n + 1) := mul_comm _ _
        _ = 1 := hcancel (n + 1)
    have hle : ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ ≤ ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1) :=
      mul_le_mul_of_nonneg_left hn2 hqk_pos.le
    rw [norm_mul, norm_zpow]
    calc ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ ≤ ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1) := hle
      _ = 1 := hkey

private theorem exists_zpow_mul_mem_annulus (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) :
    ∃ n : ℤ, ‖q * (q ^ n * u)‖₊ < 1 ∧ ‖q * (q ^ n * u)⁻¹‖₊ < 1 := by
  have hqR : ‖q‖ < 1 := nnnorm_lt_one_iff_norm.mp hq
  obtain ⟨n, h1, h2⟩ := exists_zpow_mul_norm_Ioc hq0 hqR hu0
  have hq_pos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hv_pos : (0 : ℝ) < ‖q ^ n * u‖ := lt_trans hq_pos h1
  refine ⟨n, nnnorm_lt_one_iff_norm.mpr ?_, nnnorm_lt_one_iff_norm.mpr ?_⟩
  · rw [norm_mul]
    calc ‖q‖ * ‖q ^ n * u‖ ≤ ‖q‖ * 1 := mul_le_mul_of_nonneg_left h2 hq_pos.le
      _ = ‖q‖ := mul_one _
      _ < 1 := hqR
  · rw [norm_mul, norm_inv, ← div_eq_mul_inv, div_lt_one hv_pos]
    exact h1

end TateCurve

open TateCurve

theorem solution {K : Type*} [NontriviallyNormedField K] {q u : K}
    (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) :
    ∃ n : ℤ, ‖q * (q ^ n * u)‖₊ < 1 ∧ ‖q * (q ^ n * u)⁻¹‖₊ < 1 :=
  exists_zpow_mul_mem_annulus hq0 hq hu0

end S_TateCurve_exists_zpow_mul_mem_annulus
end P2MW
export P2MW.S_TateCurve_exists_zpow_mul_mem_annulus (solution)
