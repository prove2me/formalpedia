-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.elementary_interval_bound_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:54:44.190461+00:00
-- url     : https://prove2.me/submissions/ea94785b-d013-4f23-b619-1515d0cb4400

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Theorems.Thm_SharpIntermediateSubgroupBounds_elementary_interval_bound
import Theorems.Thm_SharpIntermediateSubgroupBounds_interval_top_card_eq_one
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
theorem _root_.solution (H : Subgroup G) :
    Nat.card (interval H) ≤ H.index ^ Nat.log 2 H.index := by
  by_cases hn : 1 < H.index
  · exact elementary_interval_bound hn
  · have hpos : 0 < H.index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hi : H.index = 1 := by omega
    have htop : H = ⊤ := Subgroup.index_eq_one.mp hi
    subst H
    rw [interval_top_card_eq_one]
    simp
end SharpIntermediateSubgroupBounds
