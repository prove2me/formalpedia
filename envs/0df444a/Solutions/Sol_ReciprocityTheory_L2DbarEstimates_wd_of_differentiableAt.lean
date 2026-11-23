-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.wd_of_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:21.538208+00:00
-- url     : https://prove2.me/submissions/901057d6-539e-463d-bd9e-76548b3d1245

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
    (hf : DifferentiableAt ℂ f x) : wd n j f x = fderiv ℂ f x (bas n j) := by
  rw [wd, fderiv_real_of_complex hf, fderiv_real_of_complex hf,
    ContinuousLinearMap.map_smul, smul_eq_mul, ← mul_assoc, Complex.I_mul_I]
  ring
end ReciprocityTheory.L2DbarEstimates
