-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.fderiv_conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:39.22196+00:00
-- url     : https://prove2.me/submissions/8ca78d79-3090-4451-938e-7ecd31dac6cf

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
theorem _root_.solution {f : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x) (w : V n) :
    fderiv ℝ (fun y => conj (f y)) x w = conj (fderiv ℝ f x w) := by
  have h := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp x hf.hasFDerivAt
  rw [(show HasFDerivAt (fun y => conj (f y)) _ x from h).fderiv]
  rfl
end ReciprocityTheory.L2DbarEstimates
