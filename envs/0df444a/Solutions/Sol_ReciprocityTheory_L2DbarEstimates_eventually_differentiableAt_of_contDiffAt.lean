-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:59.058249+00:00
-- url     : https://prove2.me/submissions/15e96df6-2cf4-49a7-b785-39930be89bd5

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
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f x) : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := (hf.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by simp)
end ReciprocityTheory.L2DbarEstimates
