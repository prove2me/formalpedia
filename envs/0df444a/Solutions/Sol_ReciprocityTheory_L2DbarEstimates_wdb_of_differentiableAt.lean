-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.wdb_of_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:40.401669+00:00
-- url     : https://prove2.me/submissions/7e03d3c9-f4ba-4c53-bcbf-9636ff50c063

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_fderiv_real_of_complex

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
theorem _root_.solution {j : Fin n} {f : V n → ℂ} {x : V n}
    (hf : DifferentiableAt ℂ f x) : wdb n j f x = 0 := by
  rw [wdb, fderiv_real_of_complex hf, fderiv_real_of_complex hf,
    ContinuousLinearMap.map_smul, smul_eq_mul, ← mul_assoc, Complex.I_mul_I]
  ring
end ReciprocityTheory.L2DbarEstimates
