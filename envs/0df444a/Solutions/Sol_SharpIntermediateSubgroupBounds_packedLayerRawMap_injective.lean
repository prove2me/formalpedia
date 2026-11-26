-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.packedLayerRawMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:52:13.455852+00:00
-- url     : https://prove2.me/submissions/47d5a8cb-0bc1-4092-a6e5-9718714727ca

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.packingSubgroupDecidableEq
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupFinite
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (H : Subgroup G) (m r : ℕ) :
    Function.Injective (packedLayerRawMap H m r) := by
  rintro ⟨K, x⟩ ⟨L, y⟩ hxy
  have htuple : x.1 = y.1 := hxy
  have hKLval : K.1 = L.1 := by
    rw [← x.2.2, ← y.2.2, htuple]
  have hKL : K = L := Subtype.ext hKLval
  subst L
  have hxy' : x = y := Subtype.ext htuple
  subst y
  rfl
end SharpIntermediateSubgroupBounds
