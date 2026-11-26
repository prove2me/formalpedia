-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.manuscript_no_subquarter_elementaryAbelian_rpow_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:01:37.421795+00:00
-- url     : https://prove2.me/submissions/198d8b5d-ccf4-41b5-bc9f-1ba56050676c

import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Definitions.Def_SharpIntermediateSubgroupBounds_Manuscript
import Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_interval_card_eq
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
import Theorems.Thm_SharpIntermediateSubgroupBounds_natFloor_indexLog
import Theorems.Thm_SharpIntermediateSubgroupBounds_no_subquarter_rpow_bound
attribute [local simp] SharpIntermediateSubgroupBounds.BranchingTree.branchProduct_zero
attribute [local simp] SharpIntermediateSubgroupBounds.escapeBranchProduct_cons
attribute [local simp] SharpIntermediateSubgroupBounds.natFloor_indexLog



set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open Filter
noncomputable section
attribute [local instance] SharpIntermediateSubgroupBounds.manuscriptSubgroupIntervalFintype
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution
    {p : ℕ} [Fact p.Prime] {alpha C : ℝ} (halpha : alpha < 1 / 4) :
    ¬ ∀ a : ℕ,
      (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ) ≤
        C * Real.rpow (p : ℝ) (4 * alpha * (a : ℝ) ^ 2) := by
  intro h
  apply no_subquarter_rpow_bound (Fact.out : p.Prime).two_le halpha
  intro a
  simpa only [manuscript_elementaryAbelian_interval_card_eq] using h a
end SharpIntermediateSubgroupBounds
