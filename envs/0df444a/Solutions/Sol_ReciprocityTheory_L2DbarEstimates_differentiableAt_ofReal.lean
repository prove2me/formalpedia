-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.differentiableAt_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:15.973363+00:00
-- url     : https://prove2.me/submissions/45a60403-5a1e-4173-beb4-f73d09168c40

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
theorem _root_.solution {v : V n → ℝ} {x : V n} (hv : DifferentiableAt ℝ v x) :
    DifferentiableAt ℝ (fun y => (v y : ℂ)) x := (show HasFDerivAt (fun y => (v y : ℂ)) _ x from
    Complex.ofRealCLM.hasFDerivAt.comp x hv.hasFDerivAt).differentiableAt
end ReciprocityTheory.L2DbarEstimates
