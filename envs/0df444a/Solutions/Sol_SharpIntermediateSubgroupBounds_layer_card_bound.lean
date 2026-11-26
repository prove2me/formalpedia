-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.layer_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:03:34.836737+00:00
-- url     : https://prove2.me/submissions/18891529-0991-4a8a-8a71-8c87841860af

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Theorems.Thm_SharpIntermediateSubgroupBounds_layer_card_moment
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaQ_pos


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
    (hlo : q ^ r ≤ m) (hhi : m < q ^ (r + 1)) :
    (Nat.card (layer H m) : ℚ) ≤
      (H.index : ℚ) ^ r /
        (gammaQ q r * (m : ℚ) ^ r) := by
  have hmPos : 0 < m := lt_of_lt_of_le (pow_pos (by omega) r) hlo
  have hdenPos : (0 : ℚ) < gammaQ q r * (m : ℚ) ^ r :=
    mul_pos (gammaQ_pos hq) (pow_pos (Nat.cast_pos.mpr hmPos) _)
  apply (le_div_iff₀ hdenPos).2
  calc
    (Nat.card (layer H m) : ℚ) *
          (gammaQ q r * (m : ℚ) ^ r) =
        gammaQ q r * (Nat.card (layer H m) : ℚ) * (m : ℚ) ^ r := by
      ring
    _ ≤ (H.index : ℚ) ^ r := layer_card_moment hn hq hqp hhi
end SharpIntermediateSubgroupBounds
