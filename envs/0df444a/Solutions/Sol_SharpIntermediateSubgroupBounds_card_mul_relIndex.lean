-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.card_mul_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:42:26.03943+00:00
-- url     : https://prove2.me/submissions/c1fb7ab9-de70-4aef-b40b-bf9f62579cdd

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
theorem _root_.solution {A B : Subgroup G} (hAB : A ≤ B) :
    Nat.card A * A.relIndex B = Nat.card B := by
  have h := (A.subgroupOf B).card_mul_index
  rw [show (A.subgroupOf B).index = A.relIndex B by rfl] at h
  rw [Nat.card_congr (A.subgroupOfEquivOfLe hAB).toEquiv] at h
  exact h
end SharpIntermediateSubgroupBounds
