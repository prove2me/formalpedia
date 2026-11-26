-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.manuscript_sharpConstant_le_of_elementaryAbelian_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:05:08.983303+00:00
-- url     : https://prove2.me/submissions/f5d810b5-e763-4d79-8ff9-5dc5a3c4cd91

import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Definitions.Def_SharpIntermediateSubgroupBounds_Manuscript
import Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_interval_card_eq
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
import Theorems.Thm_SharpIntermediateSubgroupBounds_natFloor_indexLog
import Theorems.Thm_SharpIntermediateSubgroupBounds_sharpConstant_le_of_even_rank_bound
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
    {p : ℕ} [Fact p.Prime] {C : ℝ}
    (hC : ∀ a : ℕ,
      (p : ℝ)⁻¹ ^ (a * a) *
        (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ) ≤ C) :
    sharpConstant (p : ℝ) ≤ C := by
  apply sharpConstant_le_of_even_rank_bound (Fact.out : p.Prime).two_le
  intro a
  simpa only [manuscript_elementaryAbelian_interval_card_eq] using hC a
end SharpIntermediateSubgroupBounds
