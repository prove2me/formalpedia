-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.elementary_interval_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:54:06.073952+00:00
-- url     : https://prove2.me/submissions/84cdbf38-c60a-4150-85a4-301fb8cb3137

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Theorems.Thm_SharpIntermediateSubgroupBounds_cardH_pow_le_rawRelGen
import Theorems.Thm_SharpIntermediateSubgroupBounds_packed_interval_raw_card_bound
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
theorem _root_.solution {H : Subgroup G} (hn : 1 < H.index) :
    Nat.card (interval H) ≤ H.index ^ Nat.log 2 H.index := by
  let r := Nat.log 2 H.index
  have heach : ∀ K : interval H,
      Nat.card H ^ r ≤ Nat.card (RawRelGen H K.1 r) := fun K =>
    cardH_pow_le_rawRelGen K.2 (elementaryRawTuple H hn K)
  have hlower : Nat.card (interval H) * Nat.card H ^ r ≤
      ∑ K : interval H, Nat.card (RawRelGen H K.1 r) := by
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card (interval H) * Nat.card H ^ r =
          ∑ _K : interval H, Nat.card H ^ r := by
        simp
      _ ≤ ∑ K : interval H, Nat.card (RawRelGen H K.1 r) :=
        Finset.sum_le_sum fun K _ => heach K
  have hpack := packed_interval_raw_card_bound H r
  have htotal := hlower.trans hpack
  have hGcard : Nat.card H * H.index = Nat.card G := H.card_mul_index
  have hGpow : Nat.card G ^ r = Nat.card H ^ r * H.index ^ r := by
    rw [← hGcard, mul_pow]
  rw [hGpow] at htotal
  change Nat.card (interval H) ≤ H.index ^ r
  exact Nat.le_of_mul_le_mul_left (c := Nat.card H ^ r)
    (by simpa [Nat.mul_comm] using htotal)
    (pow_pos Nat.card_pos _)
end SharpIntermediateSubgroupBounds
