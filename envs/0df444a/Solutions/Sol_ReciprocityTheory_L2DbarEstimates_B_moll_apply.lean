-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.B.moll_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:30:35.739245+00:00
-- url     : https://prove2.me/submissions/48f48b78-f17d-4065-ad09-3b043cfff1bb

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
theorem _root_.solution (K : Kernel E μ) (u : E → ℂ) (x : E) :
    moll K u x = ∫ t, K.toFun t • u (x - t) ∂μ := rfl
end ReciprocityTheory.L2DbarEstimates.B
