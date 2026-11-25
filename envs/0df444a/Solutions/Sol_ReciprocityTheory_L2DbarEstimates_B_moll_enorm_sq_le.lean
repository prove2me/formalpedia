-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.B.moll_enorm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:01:56.389081+00:00
-- url     : https://prove2.me/submissions/0ef97b5d-1379-4d2c-839f-a801f8cf2b03

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_HasCompactSupport
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollEnormSqLe
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_Kernel_lintegral_ofReal

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
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) {u : E → ℂ} (hu : AEStronglyMeasurable u μ)
    (x : E) :
    ‖moll K u x‖ₑ ^ 2 ≤ ∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ^ 2 ∂μ := by
  have hK0 := K.nonneg
  have hKm : Measurable K.toFun := K.smooth.continuous.measurable
  have h1 : ‖moll K u x‖ₑ ≤ ∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ∂μ := by
    have hmoll : moll K u x = ∫ t, K.toFun t • u (x - t) ∂μ := rfl
    rw [hmoll]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun t => ?_
    rw [enorm_smul, Real.enorm_of_nonneg (hK0 t)]
  have hum : AEMeasurable (fun t => ‖u (x - t)‖ₑ) μ :=
    (hu.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left μ x)).enorm
  set f : E → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.sqrt (K.toFun t)) with hfdef
  set g : E → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.sqrt (K.toFun t)) * ‖u (x - t)‖ₑ with hgdef
  have hf : AEMeasurable f μ := hKm.sqrt.ennreal_ofReal.aemeasurable
  have hg : AEMeasurable g μ := hf.mul hum
  have r2 : ∀ z : ℝ≥0∞, z ^ (2 : ℝ) = z ^ 2 := fun z => by
    rw [← ENNReal.rpow_natCast]; norm_num
  have hsq : ∀ t, ENNReal.ofReal (Real.sqrt (K.toFun t)) ^ 2 = ENNReal.ofReal (K.toFun t) := by
    intro t
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (hK0 t)]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  have e1 : ∫⁻ t, (f * g) t ∂μ = ∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ∂μ := by
    refine lintegral_congr fun t => ?_
    simp only [Pi.mul_apply, hfdef, hgdef]
    rw [← mul_assoc, ← pow_two, hsq]
  have e2 : ∫⁻ t, f t ^ (2 : ℝ) ∂μ = 1 := by
    rw [← Kernel.lintegral_ofReal E μ K]
    refine lintegral_congr fun t => ?_
    simp only [hfdef]
    rw [r2, hsq]
  have e3 : ∫⁻ t, g t ^ (2 : ℝ) ∂μ = ∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ^ 2 ∂μ := by
    refine lintegral_congr fun t => ?_
    simp only [hgdef]
    rw [r2, mul_pow, hsq]
  rw [e1, e2, e3, ENNReal.one_rpow, one_mul] at hH
  calc ‖moll K u x‖ₑ ^ 2
      ≤ ((∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (h1.trans hH) 2
    _ = ∫⁻ t, ENNReal.ofReal (K.toFun t) * ‖u (x - t)‖ₑ ^ 2 ∂μ := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
end ReciprocityTheory.L2DbarEstimates.B
