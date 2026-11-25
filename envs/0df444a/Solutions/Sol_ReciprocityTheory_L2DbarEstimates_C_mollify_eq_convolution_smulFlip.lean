-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.mollify_eq_convolution_smulFlip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:02:01.275544+00:00
-- url     : https://prove2.me/submissions/8e28dd99-675d-49ef-9c3a-4e1e69cace17

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegConv
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_smulFlip_apply

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
theorem _root_.solution (n : ℕ) (t : ℝ) (u : V n → ℂ) :
    mollify n t u = convolution u (moll n t) smulFlip volume := by
  ext x
  simp only [mollify, convolution_def, smulFlip_apply]
end ReciprocityTheory.L2DbarEstimates.C
