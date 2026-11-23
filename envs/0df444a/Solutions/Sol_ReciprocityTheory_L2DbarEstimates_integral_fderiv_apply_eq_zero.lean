-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:45.913535+00:00
-- url     : https://prove2.me/submissions/db5adb0b-9e99-4584-9d32-35295b021249

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (n : ℕ) (H : V n → ℂ) (hH : ContDiff ℝ 1 H)
    (hc : HasCompactSupport H) (v : V n) : ∫ y, fderiv ℝ H y v = 0 := by
  have hi : Integrable (fun y => fderiv ℝ H y v) :=
    ((hH.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) v)
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := fun _ => (1 : ℂ))
    (g := H) (v := v) (by simp) (by simpa using hi)
    (by simpa using hH.continuous.integrable_of_hasCompactSupport hc)
    (fun x _ => differentiableAt_const _) (fun x _ => hH.differentiable one_ne_zero x)
  simpa using this
end ReciprocityTheory.L2DbarEstimates
