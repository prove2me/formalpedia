-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.packed_layer_raw_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:52:45.624705+00:00
-- url     : https://prove2.me/submissions/a920d0e5-5177-4385-a859-48a24f38b8cd

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Theorems.Thm_SharpIntermediateSubgroupBounds_packedLayerRawMap_injective
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
theorem _root_.solution (H : Subgroup G) (m r : ℕ) :
    (∑ K : layer H m, Nat.card (RawRelGen H K.1 r)) ≤ Nat.card G ^ r := by
  have hcard := Fintype.card_le_of_injective (packedLayerRawMap H m r)
    (packedLayerRawMap_injective H m r)
  rw [Fintype.card_sigma, Fintype.card_congr (Equiv.refl (Fin r → G))] at hcard
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fin] using hcard
end SharpIntermediateSubgroupBounds
