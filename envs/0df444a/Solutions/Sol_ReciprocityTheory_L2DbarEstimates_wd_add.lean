-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.wd_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:50.1308+00:00
-- url     : https://prove2.me/submissions/d0fa2b17-3efb-4074-aea5-6052378a85e8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt

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
theorem _root_.solution {j : Fin n} {f g : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) : wd n j (fun y => f y + g y) x = wd n j f x + wd n j g x := by
  unfold wd
  rw [(show HasFDerivAt (fun y => f y + g y) _ x from hf.hasFDerivAt.add hg.hasFDerivAt).fderiv]
  simp only [ ContinuousLinearMap.add_apply]
  ring
end ReciprocityTheory.L2DbarEstimates
