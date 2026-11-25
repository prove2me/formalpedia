-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:23:56.918007+00:00
-- url     : https://prove2.me/submissions/f02da18c-048f-45f8-b9ab-ee47222215b7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_lint_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Module
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution (Q D : ℝ) (hQ : 0 < Q) (hD : 0 < D) (c : ℂ) (s : ℝ) :
    ∫⁻ w : ℂ, ENNReal.ofReal ((Q * ‖w - c‖ ^ 2 + D) ^ (-s / 2)) =
      ENNReal.ofReal (Q⁻¹ * D ^ (1 - s / 2)) * kc s := by
  have h1 : ∫⁻ w : ℂ, ENNReal.ofReal ((Q * ‖w - c‖ ^ 2 + D) ^ (-s / 2)) =
      ∫⁻ w : ℂ, ENNReal.ofReal ((Q * ‖w‖ ^ 2 + D) ^ (-s / 2)) := by
    rw [← MeasureTheory.lintegral_add_right_eq_self (μ := (volume : Measure ℂ))
      (fun w : ℂ => ENNReal.ofReal ((Q * ‖w - c‖ ^ 2 + D) ^ (-s / 2))) c]
    simp only [add_sub_cancel_right]
  rw [h1]
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = Real.sqrt (D / Q) := ⟨_, rfl⟩
  have htpos : 0 < t := by
    rw [ht]
    exact Real.sqrt_pos.mpr (div_pos hD hQ)
  have ht2 : t ^ 2 = D / Q := by
    rw [ht]
    exact Real.sq_sqrt (div_pos hD hQ).le
  have hmeas : Measurable (fun w : ℂ => ENNReal.ofReal ((Q * ‖w‖ ^ 2 + D) ^ (-s / 2))) := by
    first
    | fun_prop
    | measurability
  have hmeas2 : Measurable (fun w : ℂ => ENNReal.ofReal ((1 + ‖w‖ ^ 2) ^ (-s / 2))) := by
    first
    | fun_prop
    | measurability
  have h2 := lint_smul (volume : Measure ℂ) hmeas htpos.ne'
  beta_reduce at h2
  rw [Complex.finrank_real_complex] at h2
  have h3 : ∀ z : ℂ, ENNReal.ofReal ((Q * ‖t • z‖ ^ 2 + D) ^ (-s / 2)) =
      ENNReal.ofReal (D ^ (-s / 2)) * ENNReal.ofReal ((1 + ‖z‖ ^ 2) ^ (-s / 2)) := by
    intro z
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, mul_pow, ht2,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _)]
    congr 1
    rw [← Real.mul_rpow hD.le (by positivity)]
    congr 1
    field_simp
    ring
  simp_rw [h3] at h2
  rw [MeasureTheory.lintegral_const_mul _ hmeas2] at h2
  have hinv : 0 < (t ^ 2)⁻¹ := inv_pos.mpr (pow_pos htpos 2)
  have h4 : ∫⁻ w : ℂ, ENNReal.ofReal ((Q * ‖w‖ ^ 2 + D) ^ (-s / 2)) =
      ENNReal.ofReal (t ^ 2) * (ENNReal.ofReal (D ^ (-s / 2)) * kc s) := by
    unfold kc
    rw [h2, ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg htpos.le 2), abs_of_pos hinv,
      mul_inv_cancel₀ (pow_pos htpos 2).ne', ENNReal.ofReal_one, one_mul]
  rw [h4, ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg htpos.le 2), ht2]
  congr 2
  rw [show (1 : ℝ) - s / 2 = 1 + (-s / 2) by ring, Real.rpow_add hD, Real.rpow_one, div_eq_mul_inv]
  ring
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
