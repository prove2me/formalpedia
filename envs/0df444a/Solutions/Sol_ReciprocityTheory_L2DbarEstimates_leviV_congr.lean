-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.leviV_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:36:21.999222+00:00
-- url     : https://prove2.me/submissions/0cbb6bbc-622f-4ff0-b5d0-7b6ba902f944

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_eventuallyEq

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
theorem _root_.solution {f g : V n → ℂ} {x : V n} (h : f =ᶠ[𝓝 x] g) (ξ : Fin n → ℂ) :
    leviV n f x ξ = leviV n g x ξ := by
  unfold leviV
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [wd_congr (wdb_eventuallyEq h)]
end ReciprocityTheory.L2DbarEstimates
