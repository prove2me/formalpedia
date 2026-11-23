-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.wd_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:30.980489+00:00
-- url     : https://prove2.me/submissions/61ef7291-40af-4e8f-a455-bb729575ecaf

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_fderiv_conj_apply

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
theorem _root_.solution {j : Fin n} {f : V n → ℂ} {x : V n} (hf : DifferentiableAt ℝ f x) :
    wd n j (fun y => conj (f y)) x = conj (wdb n j f x) := by
  simp only [wd, wdb, fderiv_conj_apply hf]
  simp [map_div₀, map_ofNat]
  all_goals ring
end ReciprocityTheory.L2DbarEstimates
