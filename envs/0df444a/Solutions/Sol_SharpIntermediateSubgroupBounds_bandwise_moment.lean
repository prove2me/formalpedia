-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.bandwise_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:57:12.966388+00:00
-- url     : https://prove2.me/submissions/17687a34-0d2d-48ca-a02e-34c39a8b09f1

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Theorems.Thm_SharpIntermediateSubgroupBounds_band_raw_sum_bound
import Theorems.Thm_SharpIntermediateSubgroupBounds_card_mul_relIndex


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
    {q : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac) (r : ℕ) :
    gammaQ q r *
        (∑ K : band H q r, (H.relIndex K.1 : ℚ) ^ r) ≤
      (H.index : ℚ) ^ r := by
  have hraw := band_raw_sum_bound hn hq hqp (r := r)
  have hsum :
      (∑ K : band H q r, (Nat.card K.1 : ℚ) ^ r) =
        (Nat.card H : ℚ) ^ r *
          (∑ K : band H q r, (H.relIndex K.1 : ℚ) ^ r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro K hK
    rw [← card_mul_relIndex K.2.1, Nat.cast_mul, mul_pow]
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
          (gammaQ q r *
            (∑ K : band H q r, (H.relIndex K.1 : ℚ) ^ r)) =
        gammaQ q r *
          (∑ K : band H q r, (Nat.card K.1 : ℚ) ^ r) := by
      rw [hsum]
      ring
    _ ≤ (Nat.card G : ℚ) ^ r := hraw
    _ = (Nat.card H : ℚ) ^ r * (H.index : ℚ) ^ r := hGpow
end SharpIntermediateSubgroupBounds
