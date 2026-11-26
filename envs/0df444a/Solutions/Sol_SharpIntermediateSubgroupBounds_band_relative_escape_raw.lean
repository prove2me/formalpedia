-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.band_relative_escape_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:55:59.886454+00:00
-- url     : https://prove2.me/submissions/528e1991-be2c-4c8b-81d5-97f0ed6e5105

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaQ_mono_base
import Theorems.Thm_SharpIntermediateSubgroupBounds_relative_escape_raw


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
    {q r : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac)
    (K : band H q r) :
    gammaQ q r * (Nat.card K.1 : ℚ) ^ r ≤
      (Nat.card (RawRelGen H K.1 r) : ℚ) := by
  have hupper : H.relIndex K.1 < H.index.minFac ^ (r + 1) :=
    K.2.2.2.trans_le (pow_le_pow_left' hqp _)
  apply le_trans
    (mul_le_mul_of_nonneg_right (gammaQ_mono_base hq hqp) (by positivity))
  exact relative_escape_raw hn K.2.1 hupper
end SharpIntermediateSubgroupBounds
