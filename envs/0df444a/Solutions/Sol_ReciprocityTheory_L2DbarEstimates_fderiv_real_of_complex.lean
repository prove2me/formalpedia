-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.fderiv_real_of_complex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:39.528796+00:00
-- url     : https://prove2.me/submissions/82e36668-8bd7-4065-9ecd-e5fd5f1be531

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
theorem _root_.solution {f : V n → ℂ} {x : V n} (hf : DifferentiableAt ℂ f x) (w : V n) :
    fderiv ℝ f x w = fderiv ℂ f x w := by
  rw [(hf.hasFDerivAt.restrictScalars ℝ).fderiv]
  rfl
end ReciprocityTheory.L2DbarEstimates
