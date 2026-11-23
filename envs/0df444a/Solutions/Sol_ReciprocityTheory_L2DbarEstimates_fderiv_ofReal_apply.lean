-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.fderiv_ofReal_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:59.101049+00:00
-- url     : https://prove2.me/submissions/aaf3aeaa-939c-445e-b9a4-9ebbcfafeb0e

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
theorem _root_.solution {v : V n → ℝ} {x : V n} (hv : DifferentiableAt ℝ v x) (w : V n) :
    fderiv ℝ (fun y => (v y : ℂ)) x w = (fderiv ℝ v x w : ℂ) := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp x hv.hasFDerivAt
  rw [(show HasFDerivAt (fun y => (v y : ℂ)) _ x from h).fderiv]
  rfl
end ReciprocityTheory.L2DbarEstimates
