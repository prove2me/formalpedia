-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.cardH_pow_le_rawRelGen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:53:11.76181+00:00
-- url     : https://prove2.me/submissions/2865ce38-f26a-423f-9c2d-2946104779d4

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Theorems.Thm_SharpIntermediateSubgroupBounds_rawHTranslate_injective
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
theorem _root_.solution {H K : Subgroup G} {r : ℕ}
    (hHK : H ≤ K) (x : RawRelGen H K r) :
    Nat.card H ^ r ≤ Nat.card (RawRelGen H K r) := by
  letI : Fintype H := Fintype.ofFinite H
  have hcard := Fintype.card_le_of_injective (rawHTranslate hHK x)
    (rawHTranslate_injective hHK x)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simpa only [Fintype.card_fun, Fintype.card_fin] using hcard
end SharpIntermediateSubgroupBounds
