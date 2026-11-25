-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.leviNonnegOn_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:58.632804+00:00
-- url     : https://prove2.me/submissions/ed8356a6-261c-4524-aadc-0a9a0bd409f4

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
theorem _root_.solution (c : ℝ) (U : Set (V n)) : LeviNonnegOn n (fun _ => c) U := by
  intro x _ ξ
  have h0 : ∀ k, wdb n k (fun _ : V n => ((c : ℝ) : ℂ)) = fun _ => 0 := fun k => by
    funext y
    simp [wdb]
  simp [leviV, h0, wd]
end ReciprocityTheory.L2DbarEstimates
