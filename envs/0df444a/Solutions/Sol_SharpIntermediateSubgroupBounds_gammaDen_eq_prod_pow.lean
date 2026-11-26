-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.gammaDen_eq_prod_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:51:12.624846+00:00
-- url     : https://prove2.me/submissions/d3fc37bd-536c-4b5c-875d-1f059bd52dbe

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
theorem _root_.solution (p r : ℕ) :
    gammaDen p r = ∏ j ∈ Finset.range r, p ^ (j + 1) := by
  rw [gammaDen, Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_range_id]
  simp only [Finset.sum_const_nat, Finset.card_range, mul_one]
  have hsucc := Finset.sum_range_id (r + 1)
  simp only [Nat.add_sub_cancel] at hsucc
  have hr := Finset.sum_range_id r
  rw [Nat.mul_comm r (r + 1), ← hsucc, ← hr, Finset.sum_range_succ]
end SharpIntermediateSubgroupBounds
