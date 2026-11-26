-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.escapeChoice_card_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:51:00.057986+00:00
-- url     : https://prove2.me/submissions/3d0b871e-80fd-4490-8929-e063a4a3fde5

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

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupDecidableEq
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (K : Subgroup G) (s : EscapeState K)
    (hs : s.1 = K) :
    Fintype.card (EscapeChoice K s) = Nat.card K := by
  letI : Fintype K := Fintype.ofFinite K
  let e : EscapeChoice K s ≃ K :=
    { toFun := fun x => x.1
      invFun := fun x => ⟨x, Or.inl hs⟩
      left_inv := by
        intro x
        apply Subtype.ext
        rfl
      right_inv := by intro x; rfl }
  rw [Fintype.card_congr e, Nat.card_eq_fintype_card]
end SharpIntermediateSubgroupBounds
