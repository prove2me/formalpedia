-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.manuscript_no_subquarter_positive_elementaryAbelian_rpow_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:02:36.80784+00:00
-- url     : https://prove2.me/submissions/feac7523-32ef-4b16-a5f4-d343bc896363

import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Definitions.Def_SharpIntermediateSubgroupBounds_Manuscript
import Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_interval_card_eq
import Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_no_subquarter_elementaryAbelian_rpow_bound
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
import Theorems.Thm_SharpIntermediateSubgroupBounds_natFloor_indexLog
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
    ¬ ∀ a : ℕ, 0 < a →
      (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ) ≤
        C * Real.rpow (p : ℝ) (4 * alpha * (a : ℝ) ^ 2) := by
  intro hpositive
  apply manuscript_no_subquarter_elementaryAbelian_rpow_bound
    (p := p) (alpha := alpha) (C := max C 1) halpha
  intro a
  by_cases ha : a = 0
  · subst a
    rw [manuscript_elementaryAbelian_interval_card_eq]
    simp [totalQBinom]
  · have haPos : 0 < a := Nat.pos_of_ne_zero ha
    have hpow : 0 ≤ Real.rpow (p : ℝ) (4 * alpha * (a : ℝ) ^ 2) :=
      Real.rpow_nonneg (by positivity) _
    exact (hpositive a haPos).trans
      (mul_le_mul_of_nonneg_right (le_max_left C 1) hpow)
end SharpIntermediateSubgroupBounds
