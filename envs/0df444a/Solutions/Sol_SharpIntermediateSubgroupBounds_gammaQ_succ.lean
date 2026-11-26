-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.gammaQ_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:52:37.146635+00:00
-- url     : https://prove2.me/submissions/cdaeed3e-e8e2-49b6-89b5-3205862eaa9c

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaQ_eq_gammaProdQ
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
theorem _root_.solution (p r : ℕ) (hp : 0 < p) :
    gammaQ p (r + 1) =
      gammaQ p r * (1 - 1 / (p : ℚ) ^ (r + 1)) := by
  rw [gammaQ_eq_gammaProdQ p (r + 1) hp,
    gammaQ_eq_gammaProdQ p r hp]
  simp [gammaProdQ, Finset.prod_range_succ]
end SharpIntermediateSubgroupBounds
