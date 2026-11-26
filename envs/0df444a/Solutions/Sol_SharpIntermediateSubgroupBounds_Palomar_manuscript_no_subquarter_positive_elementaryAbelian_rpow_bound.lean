-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.Palomar.manuscript_no_subquarter_positive_elementaryAbelian_rpow_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:06:09.717001+00:00
-- url     : https://prove2.me/submissions/4ab708c6-7d25-4aaf-82e2-506799ffb043

import Definitions.Def_SharpIntermediateSubgroupBounds
import Definitions.Def_SharpIntermediateSubgroupBounds_Solution
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
import Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_no_subquarter_positive_elementaryAbelian_rpow_bound
import Theorems.Thm_SharpIntermediateSubgroupBounds_natFloor_indexLog
attribute [local simp] SharpIntermediateSubgroupBounds.BranchingTree.branchProduct_zero
attribute [local simp] SharpIntermediateSubgroupBounds.escapeBranchProduct_cons
attribute [local simp] SharpIntermediateSubgroupBounds.natFloor_indexLog



set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open SharpIntermediateSubgroupBounds.Palomar
open scoped BigOperators Topology
open Filter Finset Real
noncomputable section
namespace SharpIntermediateSubgroupBounds.Palomar
theorem _root_.solution
    {p : ℕ} [Fact p.Prime] {alpha C : ℝ} (halpha : alpha < 1 / 4) :
    ¬ ∀ a : ℕ, 0 < a →
      (Nat.card (elementaryAbelianInterval p (2 * a)) : ℝ) ≤
        C * Real.rpow (p : ℝ) (4 * alpha * (a : ℝ) ^ 2) := by
  simpa only [← Nat.card_eq_fintype_card] using
    (SharpIntermediateSubgroupBounds.manuscript_no_subquarter_positive_elementaryAbelian_rpow_bound
      (p := p) (alpha := alpha) (C := C) halpha)
end SharpIntermediateSubgroupBounds.Palomar
