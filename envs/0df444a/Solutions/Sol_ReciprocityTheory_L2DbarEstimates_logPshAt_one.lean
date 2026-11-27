-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.logPshAt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:29:56.156623+00:00
-- url     : https://prove2.me/submissions/54ec9421-0869-4135-8a58-d20def73ee14

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_logPshAt_normSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (x : V n) : LogPshAt n (fun y => Complex.normSq ((fun _ : V n => (1 : ℂ)) y)) x :=
  logPshAt_normSq contDiffAt_const
end ReciprocityTheory.L2DbarEstimates
