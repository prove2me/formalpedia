-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.deriv_exp_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:29.022959+00:00
-- url     : https://prove2.me/submissions/4c553265-0863-4dd0-a582-8f027045203b

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
theorem _root_.solution (t : ℝ) : deriv (fun t => Real.exp (-t)) t = -Real.exp (-t) := by
  have h := (hasDerivAt_neg t).exp
  rw [h.deriv]; ring
end ReciprocityTheory.L2DbarEstimates.I
