-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.B.moll_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:29:37.071543+00:00
-- url     : https://prove2.me/submissions/ea948c49-5df7-4a8c-89f0-e8741f286488

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_HasCompactSupport
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
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : LocalSt E μ := by
  intro K u s x hs
  rw [moll_apply, moll_apply]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  by_cases ht : K.toFun t = 0
  · simp [ht]
  have htr := K.support_subset ht
  rw [mem_ball_zero_iff] at htr
  have hxt : x - t ∈ s := hs (by rw [mem_ball, dist_eq_norm]; simpa using htr)
  simp [Set.indicator_of_mem hxt]
end ReciprocityTheory.L2DbarEstimates.B
