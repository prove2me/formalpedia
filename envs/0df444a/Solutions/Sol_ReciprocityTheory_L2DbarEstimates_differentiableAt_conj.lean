-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.differentiableAt_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:29.327012+00:00
-- url     : https://prove2.me/submissions/a06f1ec5-6b02-4917-b1d4-7110b67f80cd

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
theorem _root_.solution {f : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y => conj (f y)) x := (show HasFDerivAt (fun y => conj (f y)) _ x from
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp x hf.hasFDerivAt).differentiableAt
end ReciprocityTheory.L2DbarEstimates
