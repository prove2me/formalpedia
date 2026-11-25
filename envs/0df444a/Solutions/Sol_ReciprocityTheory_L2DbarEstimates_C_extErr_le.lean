-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.extErr_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:23.655308+00:00
-- url     : https://prove2.me/submissions/5a5bca36-829f-4e7b-aab2-25d19723e18d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCut
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeak
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MollifyEqConvolution
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeak
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_fderiv_logCutoff_eq_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_norm_fderiv_logCutoff_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal ContDiff
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {F g u : V n → ℂ} {k C0 Mg : ℝ} (hk : 0 < k) (hC0 : 0 ≤ C0)
    (hC0b : ∀ t, ‖deriv extCh t‖ ≤ C0) (hMg : ∀ z, ‖g z‖ ≤ Mg) {z : V n} (v : V n)
    (hFd : DifferentiableAt ℝ F z) (hz : F z ≠ 0) :
    ‖u z * g z * extErr F k v z‖ₑ ≤ ENNReal.ofReal (Mg * (2 * ‖v‖) * C0 * k⁻¹) *
      (tsupport g ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧
        -Real.log (‖F z‖ ^ 2) ≤ 2 * k}).indicator
        (fun z => ‖u z‖ₑ * ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ₑ) z := by
  classical
  have hMg0 : 0 ≤ Mg := (norm_nonneg _).trans (hMg z)
  by_cases hmem : z ∈ tsupport g ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧
      -Real.log (‖F z‖ ^ 2) ≤ 2 * k}
  · rw [Set.indicator_apply, if_pos hmem]
    have hD := norm_fderiv_logCutoff_le hk hC0b hFd hz
    have hE : ‖extErr F k v z‖ ≤ 2 * ‖v‖ * ‖fderiv ℝ (extCut F k) z‖ := by
      unfold extErr
      calc _ ≤ ‖((fderiv ℝ (extCut F k) z (I • v) : ℝ) : ℂ)‖ +
            ‖I * ((fderiv ℝ (extCut F k) z v : ℝ) : ℂ)‖ := norm_sub_le _ _
        _ = ‖fderiv ℝ (extCut F k) z (I • v)‖ + ‖fderiv ℝ (extCut F k) z v‖ := by
            rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real]
        _ ≤ ‖fderiv ℝ (extCut F k) z‖ * ‖I • v‖ + ‖fderiv ℝ (extCut F k) z‖ * ‖v‖ :=
            add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
        _ = 2 * ‖v‖ * ‖fderiv ℝ (extCut F k) z‖ := by
            rw [norm_smul, Complex.norm_I, one_mul]; ring
    have hK : 0 ≤ Mg * (2 * ‖v‖) * C0 * k⁻¹ :=
      mul_nonneg (mul_nonneg (mul_nonneg hMg0 (by positivity)) hC0) (inv_nonneg.mpr hk.le)
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul hK]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_mul, norm_mul]
    have hE' : ‖extErr F k v z‖ ≤ 2 * ‖v‖ * (C0 * k⁻¹ *
        ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖) :=
      hE.trans (mul_le_mul_of_nonneg_left hD (by positivity))
    calc ‖u z‖ * ‖g z‖ * ‖extErr F k v z‖ ≤ ‖u z‖ * Mg * (2 * ‖v‖ * (C0 * k⁻¹ *
          ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖)) := by
          gcongr
          exact hMg z
      _ = _ := by ring
  · rw [Set.indicator_apply, if_neg hmem, mul_zero, nonpos_iff_eq_zero, enorm_eq_zero]
    by_cases hzt : z ∈ tsupport g
    · have h2 : ¬ (k ≤ -Real.log (‖F z‖ ^ 2) ∧ -Real.log (‖F z‖ ^ 2) ≤ 2 * k) :=
        fun hb => hmem ⟨hzt, hz, hb⟩
      have h3 := fderiv_logCutoff_eq_zero hk hFd hz h2
      simp [extErr, h3]
    · rw [image_eq_zero_of_notMem_tsupport hzt]
      simp
end ReciprocityTheory.L2DbarEstimates.C
