-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.intervalToBandSigma_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:52:06.592661+00:00
-- url     : https://prove2.me/submissions/10ecb22c-84c4-40e3-9659-5192eeb9515b

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
attribute [local simp] SharpIntermediateSubgroupBounds.BranchingTree.branchProduct_zero
attribute [local simp] SharpIntermediateSubgroupBounds.escapeBranchProduct_cons



set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.packingSubgroupDecidableEq
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupFinite
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (H : Subgroup G) (q : ℕ)
    (hn : 1 < H.index) (hq : 1 < q) :
    Function.Injective (intervalToBandSigma H q hn hq) := by
  intro K L h
  have := congrArg (bandSigmaToInterval H q) h
  simpa using this
end SharpIntermediateSubgroupBounds
