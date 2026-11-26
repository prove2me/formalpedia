-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.relative_escape_coset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:55:59.376439+00:00
-- url     : https://prove2.me/submissions/78285b89-8632-47f8-bd41-9c4d198e6e8c

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_rawRelGen_card_eq_cardH_pow_mul_cosetRelGen_card
import Theorems.Thm_SharpIntermediateSubgroupBounds_card_mul_relIndex
import Theorems.Thm_SharpIntermediateSubgroupBounds_relative_escape_raw

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupDecidableEq
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {H K : Subgroup G}
    (hn : 1 < H.index) (hHK : H ≤ K) {r : ℕ}
    (hhi : H.relIndex K < H.index.minFac ^ (r + 1)) :
    gammaQ H.index.minFac r * (H.relIndex K : ℚ) ^ r ≤
      (Nat.card (CosetRelGen H K r) : ℚ) := by
  have hraw := relative_escape_raw hn hHK hhi
  have hcardNat := card_mul_relIndex hHK
  have hcardQ :
      (Nat.card H : ℚ) * (H.relIndex K : ℚ) = Nat.card K := by
    exact_mod_cast hcardNat
  have hrawCardNat :=
    rawRelGen_card_eq_cardH_pow_mul_cosetRelGen_card hHK r
  have hrawCardQ :
      (Nat.card (RawRelGen H K r) : ℚ) =
        (Nat.card H : ℚ) ^ r *
          (Nat.card (CosetRelGen H K r) : ℚ) := by
    exact_mod_cast hrawCardNat
  have hmul :
      (Nat.card H : ℚ) ^ r *
          (gammaQ H.index.minFac r * (H.relIndex K : ℚ) ^ r) ≤
        (Nat.card H : ℚ) ^ r *
          (Nat.card (CosetRelGen H K r) : ℚ) := by
    calc
      (Nat.card H : ℚ) ^ r *
            (gammaQ H.index.minFac r * (H.relIndex K : ℚ) ^ r) =
          gammaQ H.index.minFac r *
            (((Nat.card H : ℚ) * H.relIndex K) ^ r) := by
              rw [mul_pow]
              ring
      _ = gammaQ H.index.minFac r * (Nat.card K : ℚ) ^ r := by
        rw [hcardQ]
      _ ≤ (Nat.card (RawRelGen H K r) : ℚ) := hraw
      _ = (Nat.card H : ℚ) ^ r *
          (Nat.card (CosetRelGen H K r) : ℚ) := hrawCardQ
  have hHpowPos : (0 : ℚ) < (Nat.card H : ℚ) ^ r := by
    exact pow_pos (Nat.cast_pos.mpr Nat.card_pos) _
  exact le_of_mul_le_mul_left hmul hHpowPos
end SharpIntermediateSubgroupBounds
