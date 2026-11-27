-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.B.mollifier_memL2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:29:26.132022+00:00
-- url     : https://prove2.me/submissions/41856dfa-e256-48ba-a759-62795c3c7b3b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_HasCompactSupport
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollEnormSqLe
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_moll_young

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
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : MollifierMemL2 E μ := by
  intro K u hu
  have hT : thickening K.r (univ : Set E) = univ :=
    eq_univ_of_forall fun x => mem_thickening_iff.mpr ⟨x, mem_univ _, by simpa using K.r_pos⟩
  have hY := moll_young E μ K u univ MeasurableSet.univ hu.1
  rw [hT, Measure.restrict_univ] at hY
  have hcs : HasCompactSupport K.toFun :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) K.r) fun x hx => by
      by_contra h
      exact hx (ball_subset_closedBall (K.support_subset h))
  have hc : Continuous (moll K u) :=
    hcs.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) K.smooth.continuous
      (hu.locallyIntegrable (by norm_num))
  exact ⟨⟨hc.aestronglyMeasurable, hY.trans_lt hu.2⟩, hY⟩
end ReciprocityTheory.L2DbarEstimates.B
