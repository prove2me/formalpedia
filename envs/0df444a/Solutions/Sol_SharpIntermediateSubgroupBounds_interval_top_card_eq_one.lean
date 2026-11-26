-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.interval_top_card_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:52:51.596837+00:00
-- url     : https://prove2.me/submissions/2d33ad90-cf3f-4a9a-ba4f-e73ed12ee1c4

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
theorem _root_.solution :
    Nat.card (interval (⊤ : Subgroup G)) = 1 := by
  let e : interval (⊤ : Subgroup G) ≃ PUnit.{u + 1} :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => ⟨⊤, le_rfl⟩
      left_inv := by
        intro K
        apply Subtype.ext
        exact (top_unique K.2).symm
      right_inv := by intro z; cases z; rfl }
  rw [Nat.card_congr e]
  simp
end SharpIntermediateSubgroupBounds
