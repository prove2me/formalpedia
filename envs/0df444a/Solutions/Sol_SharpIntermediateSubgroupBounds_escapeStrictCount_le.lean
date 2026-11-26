-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.escapeStrictCount_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:51:15.354423+00:00
-- url     : https://prove2.me/submissions/cd6a054d-5ced-40c8-992a-2daaeb361aab

import Definitions.Def_SharpIntermediateSubgroupBounds_Tree
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
attribute [local simp] SharpIntermediateSubgroupBounds.BranchingTree.branchProduct_zero



set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupDecidableEq
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (K : Subgroup G) {r : ℕ} {s : EscapeState K}
    (z : EscapePath K r s) : escapeStrictCount K z ≤ r := by
  induction r generalizing s with
  | zero => simp [escapeStrictCount]
  | succ r ih =>
      obtain ⟨x, z⟩ := z
      change escapeStrictCount K (escapeCons K x z) ≤ r + 1
      rw [escapeStrictCount_cons]
      split_ifs <;> specialize ih z <;> omega
end SharpIntermediateSubgroupBounds
