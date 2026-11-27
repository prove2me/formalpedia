-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.B.Kernel.eq_zero_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:29:05.044108+00:00
-- url     : https://prove2.me/submissions/97787d0a-61fc-4124-840a-3e283a5fb39e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_HasCompactSupport

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
namespace ReciprocityTheory.L2DbarEstimates.B
namespace Kernel
theorem _root_.solution (K : Kernel E μ) {t : E} (ht : K.r ≤ ‖t‖) : K.toFun t = 0 := by
  by_contra h
  have h' := K.support_subset h
  rw [mem_ball_zero_iff] at h'
  linarith
end Kernel
end ReciprocityTheory.L2DbarEstimates.B
