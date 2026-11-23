-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.norm_exp_mul_I_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:38.835594+00:00
-- url     : https://prove2.me/submissions/e601a98f-7aa5-46c2-9922-575786a6e4cc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Circle
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MeasurableEmbeddingRotAbout

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution (θ : ℝ) : ‖Complex.exp ((θ : ℂ) * I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ
end ReciprocityTheory.L2DbarEstimates.C
