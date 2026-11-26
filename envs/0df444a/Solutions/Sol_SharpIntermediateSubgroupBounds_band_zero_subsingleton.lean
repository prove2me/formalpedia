-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.band_zero_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:52:23.969252+00:00
-- url     : https://prove2.me/submissions/30e9f586-5861-4923-a296-34d519ebd6f7

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Theorems.Thm_SharpIntermediateSubgroupBounds_band_zero_eq_bottom

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.packingSubgroupDecidableEq
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupFinite
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {H : Subgroup G} {q : ℕ}
    (hq : 1 < q) (hqp : q ≤ H.index.minFac) (K L : band H q 0) :
    K = L := by
  apply Subtype.ext
  rw [band_zero_eq_bottom hq hqp K, band_zero_eq_bottom hq hqp L]
end SharpIntermediateSubgroupBounds
