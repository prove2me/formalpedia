-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.deriv_neg_exp_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:14:52.428453+00:00
-- url     : https://prove2.me/submissions/3c3b1da9-e194-4d2b-b8cc-21d905a9f4d3

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open scoped ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (t : ℝ) : deriv (fun t => -Real.exp (-t)) t = Real.exp (-t) := by
  have h : HasDerivAt (fun t => -Real.exp (-t)) (-(Real.exp (-t) * -1)) t :=
    (hasDerivAt_neg t).exp.neg
  rw [h.deriv]; ring
end ReciprocityTheory.L2DbarEstimates.I
