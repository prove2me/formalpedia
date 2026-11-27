-- Prove2me | solution 1 for TreeStack.exists_two_le_of_card_lt_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:10:20.836324+00:00
-- url     : https://prove2.me/submissions/3a375de1-18c8-4e2b-b7c3-dc68141eadbe

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_PebblingMove
import Theorems.Thm_TreeStack_oneOn_apply
import Theorems.Thm_TreeStack_mass_oneOn
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff


attribute [local simp] TreeStack.oneOn_apply
attribute [local simp] TreeStack.mass_oneOn

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution {V : Type*} [Fintype V]
    (C : Configuration V) (h : Fintype.card V < mass C) :
    ∃ v, 2 ≤ C v := by
  by_contra hn
  push Not at hn
  have hmass : mass C ≤ Fintype.card V := by
    rw [mass]
    calc
      (∑ v, C v) ≤ ∑ _v : V, 1 := Finset.sum_le_sum fun v _ => by
        have hv := hn v
        omega
      _ = Fintype.card V := by simp
  omega
end TreeStack
