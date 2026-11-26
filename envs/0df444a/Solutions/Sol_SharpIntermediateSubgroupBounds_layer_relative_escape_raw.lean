-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.layer_relative_escape_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:56:04.433538+00:00
-- url     : https://prove2.me/submissions/017a43b8-e8f6-4881-a213-7e688a556e79

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
    {q r m : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac)
    (hmi : m < q ^ (r + 1)) (K : layer H m) :
    gammaQ q r * (Nat.card K.1 : ℚ) ^ r ≤
      (Nat.card (RawRelGen H K.1 r) : ℚ) := by
  have hupper : H.relIndex K.1 < H.index.minFac ^ (r + 1) := by
    rw [K.2.2]
    exact hmi.trans_le (pow_le_pow_left' hqp _)
  apply le_trans
    (mul_le_mul_of_nonneg_right (gammaQ_mono_base hq hqp) (by positivity))
  exact relative_escape_raw hn K.2.1 hupper
end SharpIntermediateSubgroupBounds
