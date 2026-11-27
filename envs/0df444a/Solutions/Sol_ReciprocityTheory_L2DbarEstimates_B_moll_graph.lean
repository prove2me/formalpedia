-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.B.moll_graph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:29:32.246129+00:00
-- url     : https://prove2.me/submissions/eda41569-2b46-4da6-8bb0-300e9a7a1e22

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollTendstoOfContinuous
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_FderivMollApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollGraph
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_moll_l2Tendsto
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_moll_weakComm


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
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (ι : Type*) : GraphSt E μ ι := by
  intro l K hK m c v g w hw hg hw2
  refine ⟨fun k => moll_l2Tendsto E μ ι l K hK (g k) (hg k), ?_⟩
  refine (moll_l2Tendsto E μ ι l K hK w hw2).congr ?_
  intro i
  rw [moll_weakComm E μ m c v g w hw (K i)]
end ReciprocityTheory.L2DbarEstimates.B
