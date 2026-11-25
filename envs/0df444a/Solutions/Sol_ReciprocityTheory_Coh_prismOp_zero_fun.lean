-- Prove2me | solution 1 for ReciprocityTheory.Coh.prismOp_zero_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:03:24.951908+00:00
-- url     : https://prove2.me/submissions/b1238dc1-397d-42b0-9d0d-8851a12b80c5

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Theorems.Thm_ReciprocityTheory_Coh_prismOp_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Function
universe u
variable {V X Y : Type u} [AddCommGroup V]
namespace ReciprocityTheory.Coh
theorem _root_.solution (a b : X → Y) (n : ℕ) : ∀ (x : Fin (n + 1) → X),
    prismOp a b n (fun _ => (0 : V)) x = 0 := by
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; rw [prismOp_succ, ih, sub_zero]
end ReciprocityTheory.Coh
