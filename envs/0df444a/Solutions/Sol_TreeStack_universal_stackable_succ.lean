-- Prove2me | solution 1 for TreeStack.universal_stackable_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:14:19.335795+00:00
-- url     : https://prove2.me/submissions/42801a02-206f-4ec7-8a8b-8ed7994a1bf1

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_PebblingMove
import Theorems.Thm_TreeStack_mass_move_add_one
import Theorems.Thm_TreeStack_stackable_of_step
import Theorems.Thm_TreeStack_oneOn_apply
import Theorems.Thm_TreeStack_mass_oneOn
import Theorems.Thm_TreeStack_universal_stackable_gt_card
import Theorems.Thm_TreeStack_exists_two_le_of_card_lt_mass
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff


attribute [local simp] TreeStack.oneOn_apply
attribute [local simp] TreeStack.mass_oneOn

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V]
    [Nontrivial V] {G : SimpleGraph V} {t : ℕ}
    (hconn : G.Connected) (hU : UniversalStackable G t) (ht : 2 ≤ t) :
    UniversalStackable G (t + 1) := by
  intro C hCmass
  by_cases hstack : Stackable G C
  · exact hstack
  have hcard : Fintype.card V < t := universal_stackable_gt_card hU ht
  have hmassgt : Fintype.card V < mass C := by omega
  obtain ⟨u, hu⟩ := exists_two_le_of_card_lt_mass C hmassgt
  obtain ⟨v, huv⟩ := hconn.preconnected.exists_adj_of_nontrivial u
  let D := move C u v
  have hstep : PebbleStep G C D := ⟨u, v, huv, hu, rfl⟩
  have hdrop := mass_move_add_one C huv.ne hu
  have hDmass : mass D = t := by
    dsimp [D] at hdrop ⊢
    omega
  exact stackable_of_step hstep (hU D hDmass)
end TreeStack
