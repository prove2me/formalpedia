-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.wd_ofReal_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:21.290159+00:00
-- url     : https://prove2.me/submissions/67a8b770-1f8e-4d4f-b2ab-9e86202a5e8c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_differentiableAt_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_sum


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
theorem _root_.solution {m : ℕ} {j : Fin n} {u : Fin m → V n → ℝ} {x : V n}
    (hu : ∀ i, DifferentiableAt ℝ (u i) x) :
    wd n j (fun y => ((∑ i, u i y : ℝ) : ℂ)) x = ∑ i, wd n j (fun y => (u i y : ℂ)) x := by
  have hf : (fun y => ((∑ i, u i y : ℝ) : ℂ)) = fun y => ∑ i, (u i y : ℂ) := by
    funext y; push_cast; rfl
  rw [hf, wd_sum Finset.univ (fun i _ => differentiableAt_ofReal (hu i))]
end ReciprocityTheory.L2DbarEstimates
