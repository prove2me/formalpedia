-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.B.Kernel.lintegral_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:30:35.183743+00:00
-- url     : https://prove2.me/submissions/75d3ed2a-2694-40f4-8e3b-03f0f6981d7c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_HasCompactSupport
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollEnormSqLe

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
namespace Kernel
theorem _root_.solution (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) :
    ∫⁻ t, ENNReal.ofReal (K.toFun t) ∂μ = 1 := by
  have hint : Integrable K.toFun μ :=
    Integrable.of_integral_ne_zero (by rw [K.integral_eq_one]; exact one_ne_zero)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall K.nonneg),
    K.integral_eq_one, ENNReal.ofReal_one]
end Kernel
end ReciprocityTheory.L2DbarEstimates.B
