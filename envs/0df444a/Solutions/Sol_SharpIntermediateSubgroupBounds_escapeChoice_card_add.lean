-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.escapeChoice_card_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:51:03.752157+00:00
-- url     : https://prove2.me/submissions/b7be589c-5498-46af-b549-d5ff05f37c29

import Definitions.Def_SharpIntermediateSubgroupBounds_Tree
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
attribute [local simp] SharpIntermediateSubgroupBounds.BranchingTree.branchProduct_zero



set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupDecidableEq
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (K : Subgroup G) (s : EscapeState K)
    (hs : s.1 ≠ K) :
    Fintype.card (EscapeChoice K s) + Nat.card s.1 = Nat.card K := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype s.1 := Fintype.ofFinite s.1
  letI : Fintype {x : K // (x.1 : G) ∈ s.1} := Fintype.ofFinite _
  letI : Fintype {x : K // (x.1 : G) ∉ s.1} := Fintype.ofFinite _
  let ecompl : EscapeChoice K s ≃ {x : K // (x.1 : G) ∉ s.1} :=
    { toFun := fun x => ⟨x.1, x.2.resolve_left hs⟩
      invFun := fun x => ⟨x.1, Or.inr x.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        rfl }
  let emem : {x : K // (x.1 : G) ∈ s.1} ≃ s.1 :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun x => ⟨⟨x.1, s.2 x.2⟩, x.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        rfl }
  have hmem : Fintype.card {x : K // (x.1 : G) ∈ s.1} = Nat.card s.1 := by
    rw [Fintype.card_congr emem, Nat.card_eq_fintype_card]
  have hle : Fintype.card {x : K // (x.1 : G) ∈ s.1} ≤ Fintype.card K :=
    Fintype.card_subtype_le _
  rw [Fintype.card_congr ecompl, Fintype.card_subtype_compl, hmem]
  have hcancel := Nat.sub_add_cancel (by simpa [hmem] using hle)
  simpa only [Nat.card_eq_fintype_card] using hcancel
end SharpIntermediateSubgroupBounds
