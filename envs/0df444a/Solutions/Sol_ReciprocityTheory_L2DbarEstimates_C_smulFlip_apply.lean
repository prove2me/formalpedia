-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.smulFlip_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:13.689956+00:00
-- url     : https://prove2.me/submissions/ad7fb953-781a-4d6f-a768-999d5b82ef9e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegConv

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
theorem _root_.solution (a : ℂ) (r : ℝ) : smulFlip a r = (r : ℂ) * a := by
  simp only [smulFlip, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
    Complex.real_smul]
end ReciprocityTheory.L2DbarEstimates.C
