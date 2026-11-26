-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.layer_raw_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:56:33.10557+00:00
-- url     : https://prove2.me/submissions/8f7eed0f-312d-4401-bea3-c619381aaa97

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Theorems.Thm_SharpIntermediateSubgroupBounds_packed_layer_raw_card_bound
import Theorems.Thm_SharpIntermediateSubgroupBounds_layer_relative_escape_raw

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
    gammaQ q r *
        (∑ K : layer H m, (Nat.card K.1 : ℚ) ^ r) ≤
      (Nat.card G : ℚ) ^ r := by
  calc
    gammaQ q r * (∑ K : layer H m, (Nat.card K.1 : ℚ) ^ r) =
        ∑ K : layer H m,
          gammaQ q r * (Nat.card K.1 : ℚ) ^ r := by
      rw [Finset.mul_sum]
    _ ≤ ∑ K : layer H m,
        (Nat.card (RawRelGen H K.1 r) : ℚ) :=
      Finset.sum_le_sum fun K _ => layer_relative_escape_raw hn hq hqp hmi K
    _ ≤ (Nat.card G : ℚ) ^ r := by
      exact_mod_cast packed_layer_raw_card_bound H m r
end SharpIntermediateSubgroupBounds
