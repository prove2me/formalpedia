-- Prove2me | solution 1 for card_rest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:11.054935+00:00
-- url     : https://prove2.me/submissions/d2e680d6-f6e1-4a5d-872b-4410cb921c95

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics
import Theorems.Thm_card_pair

set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {x y : α}
theorem _root_.solution (hne : x ≠ y) :
    Fintype.card {z : α // z ≠ x ∧ z ≠ y} = Fintype.card α - 2 := by
  have := Fintype.card_subtype_compl (fun z : α => z = x ∨ z = y)
  have heq : {z : α // ¬(z = x ∨ z = y)} ≃ {z : α // z ≠ x ∧ z ≠ y} :=
    { toFun := fun z => ⟨z.1, by simpa [not_or] using z.2⟩
      invFun := fun z => ⟨z.1, by simpa [not_or] using z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.card_congr heq, this, card_pair hne]
