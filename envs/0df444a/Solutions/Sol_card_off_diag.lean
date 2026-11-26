-- Prove2me | solution 1 for card_off_diag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:46.590087+00:00
-- url     : https://prove2.me/submissions/bc876a01-0951-4fd4-be44-4af790dfc1f2

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
theorem _root_.solution :
    Fintype.card {p : α × α // p.1 ≠ p.2} =
      Fintype.card α * (Fintype.card α - 1) := by
  have hdiag : Fintype.card {p : α × α // p.1 = p.2} = Fintype.card α :=
    Fintype.card_congr
      { toFun := fun p : {p : α × α // p.1 = p.2} => p.1.1
        invFun := fun x => ⟨(x, x), rfl⟩
        left_inv := fun p => Subtype.ext (Prod.ext rfl p.2)
        right_inv := fun _ => rfl }
  have hne : {p : α × α // p.1 ≠ p.2} ≃ {p : α × α // ¬(p.1 = p.2)} :=
    Equiv.subtypeEquivRight fun _ => Iff.rfl
  rw [Fintype.card_congr hne, Fintype.card_subtype_compl (fun p : α × α => p.1 = p.2),
    Fintype.card_prod, hdiag]
  exact (Nat.mul_sub_one (Fintype.card α) (Fintype.card α)).symm
