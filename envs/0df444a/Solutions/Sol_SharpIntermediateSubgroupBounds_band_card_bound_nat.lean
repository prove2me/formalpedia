-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.band_card_bound_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:03:02.545635+00:00
-- url     : https://prove2.me/submissions/b58ec9de-57dc-4576-96cb-026be2dcbf4a

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Theorems.Thm_SharpIntermediateSubgroupBounds_bandwise_moment_nat
import Theorems.Thm_SharpIntermediateSubgroupBounds_band_card_mul_pow_le_moment

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
    gammaNum q r * (Nat.card (band H q r) * q ^ (r * r)) ≤
      gammaDen q r * H.index ^ r := by
  exact (Nat.mul_le_mul_left _ (band_card_mul_pow_le_moment H q r)).trans
    (bandwise_moment_nat hn hq hqp r)
end SharpIntermediateSubgroupBounds
