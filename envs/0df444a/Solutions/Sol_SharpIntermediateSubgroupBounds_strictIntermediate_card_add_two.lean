-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.strictIntermediate_card_add_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:52:56.64823+00:00
-- url     : https://prove2.me/submissions/32228816-1675-4b8e-8b67-e69dd77e169f

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
attribute [local simp] SharpIntermediateSubgroupBounds.BranchingTree.branchProduct_zero
attribute [local simp] SharpIntermediateSubgroupBounds.escapeBranchProduct_cons



set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.packingSubgroupDecidableEq
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupFinite
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (H : Subgroup G) (hHt : H < ⊤) :
    Nat.card (strictIntermediate H) + 2 = Nat.card (interval H) := by
  letI : Fintype (strictIntermediate H ⊕ Bool) := inferInstance
  have hcard := Fintype.card_congr (intervalStrictEquiv H hHt)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simpa using hcard.symm
end SharpIntermediateSubgroupBounds
