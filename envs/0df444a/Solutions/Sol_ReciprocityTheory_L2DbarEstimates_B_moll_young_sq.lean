-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.B.moll_young_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:13:29.816084+00:00
-- url     : https://prove2.me/submissions/64bcdf48-4c98-49a1-be24-f9ad631747d5

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_HasCompactSupport
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollEnormSqLe
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_Kernel_lintegral_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_moll_enorm_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.B
open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise
namespace ReciprocityTheory.L2DbarEstimates.B
theorem _root_.solution (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) (u : E → ℂ) (s : Set E) (hs : MeasurableSet s)
    (hu : AEStronglyMeasurable u μ) :
    ∫⁻ x in s, ‖moll K u x‖ₑ ^ 2 ∂μ ≤ ∫⁻ y in thickening K.r s, ‖u y‖ₑ ^ 2 ∂μ := by
  set T := thickening K.r s with hTdef
  have hT : MeasurableSet T := isOpen_thickening.measurableSet
  have hKm : Measurable K.toFun := K.smooth.continuous.measurable
  set F : E → E → ℝ≥0∞ := fun x t => ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ^ 2 with hFdef
  have hF : AEMeasurable (Function.uncurry F) ((μ.restrict s).prod μ) := by
    have hq := hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub μ μ)
    have hF0 : AEMeasurable (Function.uncurry F) (μ.prod μ) :=
      (hKm.comp measurable_snd).ennreal_ofReal.aemeasurable.mul (hq.enorm.pow_const 2)
    exact hF0.mono_ac (Measure.restrict_le_self.absolutelyContinuous.prod
      (Measure.AbsolutelyContinuous.refl μ))
  have htrans : ∀ t, ∫⁻ x in (fun x => x - t) ⁻¹' T, ‖u (x - t)‖ₑ ^ 2 ∂μ =
      ∫⁻ y in T, ‖u y‖ₑ ^ 2 ∂μ := by
    intro t
    rw [← lintegral_indicator (hT.preimage (measurable_sub_const t)), ← lintegral_indicator hT,
      ← lintegral_sub_right_eq_self (T.indicator fun y => ‖u y‖ₑ ^ 2) t]
    refine lintegral_congr fun x => ?_
    first
    | rfl
    | (by_cases hx : x - t ∈ T <;> simp [Set.indicator_apply, hx])
  have hpt : ∀ t, ∫⁻ x in s, F x t ∂μ ≤ ENNReal.ofReal (K.toFun t) * ∫⁻ y in T, ‖u y‖ₑ ^ 2 ∂μ := by
    intro t
    simp only [hFdef]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    by_cases h0 : K.toFun t = 0
    · simp [h0]
    · have ht : t ∈ ball (0 : E) K.r := K.support_subset h0
      refine mul_le_mul' le_rfl ?_
      rw [← htrans t]
      refine lintegral_mono_set fun x hx => ?_
      simp only [Set.mem_preimage, hTdef]
      refine mem_thickening_iff.mpr ⟨x, hx, ?_⟩
      rw [mem_ball_zero_iff] at ht
      simpa [dist_eq_norm] using ht
  calc ∫⁻ x in s, ‖moll K u x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x in s, ∫⁻ t, F x t ∂μ ∂μ :=
        lintegral_mono fun x => moll_enorm_sq_le E μ K hu x
    _ = ∫⁻ t, ∫⁻ x in s, F x t ∂μ ∂μ := lintegral_lintegral_swap hF
    _ ≤ ∫⁻ t, ENNReal.ofReal (K.toFun t) * ∫⁻ y in T, ‖u y‖ₑ ^ 2 ∂μ ∂μ := lintegral_mono hpt
    _ = ∫⁻ y in T, ‖u y‖ₑ ^ 2 ∂μ := by
        rw [lintegral_mul_const _ hKm.ennreal_ofReal, Kernel.lintegral_ofReal E μ K, one_mul]
end ReciprocityTheory.L2DbarEstimates.B
