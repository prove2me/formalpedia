-- Prove2me | solution 1 for card_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:31.3428+00:00
-- url     : https://prove2.me/submissions/de5f4057-5d5d-43de-b746-af9efbf5f4fc

import Definitions.Def_CARDB
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_CARDB_Asymptotics

set_option autoImplicit true
open Set TopologicalSpace
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {x y : α}
theorem _root_.solution (hne : x ≠ y) :
    Fintype.card {z : α // z = x ∨ z = y} = 2 := by
  refine (Fintype.card_congr
    { toFun := fun z : {z : α // z = x ∨ z = y} => decide (z.1 = x)
      invFun := fun b => if b then ⟨x, Or.inl rfl⟩ else ⟨y, Or.inr rfl⟩
      left_inv := fun z => by
        apply Subtype.ext
        rcases z.2 with h | h
        · simp [h]
        · have : decide (y = x) = false := decide_eq_false (Ne.symm hne)
          simp [h, this]
      right_inv := fun b => by
        cases b
        · simp [Ne.symm hne]
        · simp }).trans
    (by decide : Fintype.card Bool = 2)
