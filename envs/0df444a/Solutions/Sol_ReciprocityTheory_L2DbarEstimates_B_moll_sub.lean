-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.B.moll_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:29:45.42978+00:00
-- url     : https://prove2.me/submissions/8b4f56ad-6bf5-4237-bf2b-f4c8f1dfd287

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_HasCompactSupport
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_Kernel_hasCompactSupport
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_moll_apply

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
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) {u u' : E → ℂ} (hu : LocallyIntegrable u μ)
    (hu' : LocallyIntegrable u' μ) : moll K (u - u') = moll K u - moll K u' := by
  funext x
  have h1 := K.hasCompactSupport.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
    K.smooth.continuous hu x
  have h2 := K.hasCompactSupport.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
    K.smooth.continuous hu' x
  simp only [Pi.sub_apply, moll_apply, smul_sub]
  exact integral_sub h1 h2
end ReciprocityTheory.L2DbarEstimates.B
