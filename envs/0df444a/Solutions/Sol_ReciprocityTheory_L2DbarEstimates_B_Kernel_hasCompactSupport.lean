-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.B.Kernel.hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:33:32.173368+00:00
-- url     : https://prove2.me/submissions/80767700-004e-42e1-b33d-c2268feac80d

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
theorem _root_.solution (K : Kernel E μ) : HasCompactSupport K.toFun :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) K.r) fun x hx => by
    by_contra h
    exact hx (ball_subset_closedBall (K.support_subset h))
end Kernel
end ReciprocityTheory.L2DbarEstimates.B
