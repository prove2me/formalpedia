-- Prove2me | solution 1 for ReciprocityTheory.Coh.prismOp_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:55:21.508286+00:00
-- url     : https://prove2.me/submissions/6533b2cd-b428-4e68-8278-ddd81c47d147

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
theorem _root_.solution (a b : X → Y) (n : ℕ) : ∀ (F G : (Fin (n + 2) → Y) → V) (x : Fin (n + 1) → X),
    prismOp a b n (fun y => F y - G y) x = prismOp a b n F x - prismOp a b n G x := by
  induction n with
  | zero => intro F G x; rfl
  | succ n ih =>
    intro F G x
    rw [prismOp_succ, prismOp_succ, prismOp_succ, ih]
    abel
end ReciprocityTheory.Coh
