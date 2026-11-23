-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.wd_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:25.982928+00:00
-- url     : https://prove2.me/submissions/1141c540-35b1-47f0-8fdc-b21365aceb80

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
    (hg : DifferentiableAt ℝ g x) :
    wd n j (fun y => f y * g y) x = wd n j f x * g x + f x * wd n j g x := by
  unfold wd
  rw [(show HasFDerivAt (fun y => f y * g y) _ x from hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [ ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring
end ReciprocityTheory.L2DbarEstimates
