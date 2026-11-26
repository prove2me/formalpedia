-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.layer_card_bound_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:03:19.564404+00:00
-- url     : https://prove2.me/submissions/8feb97be-0e61-481e-99e3-bbb2dbc4e23d

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Theorems.Thm_SharpIntermediateSubgroupBounds_layer_card_moment

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
    gammaNum q r * (Nat.card (layer H m) * m ^ r) ≤
      gammaDen q r * H.index ^ r := by
  have hdenPos : 0 < gammaDen q r := pow_pos (by omega) _
  have h := layer_card_moment hn hq hqp hmi
  rw [gammaQ] at h
  have hqRat :
      (gammaNum q r : ℚ) *
          ((Nat.card (layer H m) : ℚ) * (m : ℚ) ^ r) ≤
        (gammaDen q r : ℚ) * (H.index : ℚ) ^ r := by
    calc
      (gammaNum q r : ℚ) *
            ((Nat.card (layer H m) : ℚ) * (m : ℚ) ^ r) =
          (gammaDen q r : ℚ) *
            ((gammaNum q r : ℚ) / gammaDen q r *
              (Nat.card (layer H m) : ℚ) * (m : ℚ) ^ r) := by
        field_simp
      _ ≤ (gammaDen q r : ℚ) * (H.index : ℚ) ^ r :=
        mul_le_mul_of_nonneg_left h (by positivity)
  exact_mod_cast hqRat
end SharpIntermediateSubgroupBounds
