-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.rawHTranslate_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:52:29.42071+00:00
-- url     : https://prove2.me/submissions/cb1fdb71-7a8d-4219-9c20-14faad33f418

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
theorem _root_.solution {H K : Subgroup G} {r : ℕ}
    (hHK : H ≤ K) (x : RawRelGen H K r) :
    Function.Injective (rawHTranslate hHK x) := by
  intro h k heq
  funext i
  apply Subtype.ext
  have hi := congrFun (congrArg Subtype.val heq) i
  exact mul_left_cancel hi
end SharpIntermediateSubgroupBounds
