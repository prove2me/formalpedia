-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.band_card_mul_pow_le_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:45:13.687421+00:00
-- url     : https://prove2.me/submissions/de35bdec-9bce-497e-9908-942ebaaa9cd0

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
theorem _root_.solution (H : Subgroup G) (q r : ℕ) :
    Nat.card (band H q r) * q ^ (r * r) ≤
      ∑ K : band H q r, H.relIndex K.1 ^ r := by
  have hsum : (∑ _K : band H q r, q ^ (r * r)) ≤
      ∑ K : band H q r, H.relIndex K.1 ^ r := by
    apply Finset.sum_le_sum
    intro K hK
    change q ^ (r * r) ≤ H.relIndex K.1 ^ r
    rw [pow_mul]
    exact pow_le_pow_left' K.2.2.1 _
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card (band H q r) * q ^ (r * r) =
        ∑ _K : band H q r, q ^ (r * r) := by
      simp [Nat.mul_comm]
    _ ≤ ∑ K : band H q r, H.relIndex K.1 ^ r := hsum
end SharpIntermediateSubgroupBounds
