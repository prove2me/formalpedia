-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.layer_card_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:57:09.528872+00:00
-- url     : https://prove2.me/submissions/5e263781-3b20-46fb-9216-69d0ff28457c

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Theorems.Thm_SharpIntermediateSubgroupBounds_layer_raw_sum_bound
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_card_mul_relIndex
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
theorem _root_.solution {H : Subgroup G} (hn : 1 < H.index)
    {q r m : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac)
    (hmi : m < q ^ (r + 1)) :
    gammaQ q r * (Nat.card (layer H m) : ℚ) * (m : ℚ) ^ r ≤
      (H.index : ℚ) ^ r := by
  have hraw := layer_raw_sum_bound hn hq hqp hmi
  have hsum :
      (∑ K : layer H m, (Nat.card K.1 : ℚ) ^ r) =
        (Nat.card H : ℚ) ^ r *
          (∑ K : layer H m, (H.relIndex K.1 : ℚ) ^ r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro K hK
    rw [← card_mul_relIndex K.2.1, Nat.cast_mul, mul_pow]
  have hlayerSum :
      (∑ K : layer H m, (H.relIndex K.1 : ℚ) ^ r) =
        (Nat.card (layer H m) : ℚ) * (m : ℚ) ^ r := by
    calc
      (∑ K : layer H m, (H.relIndex K.1 : ℚ) ^ r) =
          ∑ _K : layer H m, (m : ℚ) ^ r := by
        apply Finset.sum_congr rfl
        intro K hK
        rw [K.2.2]
      _ = (Nat.card (layer H m) : ℚ) * (m : ℚ) ^ r := by
        simp [Nat.card_eq_fintype_card]
  have hGcard : Nat.card H * H.index = Nat.card G := H.card_mul_index
  have hGpow :
      (Nat.card G : ℚ) ^ r =
        (Nat.card H : ℚ) ^ r * (H.index : ℚ) ^ r := by
    rw [← hGcard, Nat.cast_mul, mul_pow]
  have hHpos : (0 : ℚ) < (Nat.card H : ℚ) ^ r :=
    pow_pos (Nat.cast_pos.mpr Nat.card_pos) _
  apply le_of_mul_le_mul_left _ hHpos
  calc
    (Nat.card H : ℚ) ^ r *
          (gammaQ q r * (Nat.card (layer H m) : ℚ) * (m : ℚ) ^ r) =
        gammaQ q r *
          (∑ K : layer H m, (Nat.card K.1 : ℚ) ^ r) := by
      rw [hsum, hlayerSum]
      ring
    _ ≤ (Nat.card G : ℚ) ^ r := hraw
    _ = (Nat.card H : ℚ) ^ r * (H.index : ℚ) ^ r := hGpow
end SharpIntermediateSubgroupBounds
