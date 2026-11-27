-- Prove2me | solution 1 for TreeStack.universal_stackable_gt_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:12:35.395718+00:00
-- url     : https://prove2.me/submissions/3b27e254-f88c-487c-b17e-b582da33066d

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_PebblingMove
import Theorems.Thm_TreeStack_oneOn_apply
import Theorems.Thm_TreeStack_mass_oneOn
import Theorems.Thm_TreeStack_not_stackable_oneOn_of_two_le_card
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff


attribute [local simp] TreeStack.oneOn_apply
attribute [local simp] TreeStack.mass_oneOn

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {t : ℕ} (hU : UniversalStackable G t) (ht : 2 ≤ t) :
    Fintype.card V < t := by
  by_contra h
  have hle : t ≤ Fintype.card V := Nat.le_of_not_gt h
  obtain ⟨s, -, hs⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset V)) (by simpa using hle)
  have hm : mass (oneOn s) = t := by simpa [hs]
  exact not_stackable_oneOn_of_two_le_card (G := G) (s := s) (by omega)
    (hU (oneOn s) hm)
end TreeStack
