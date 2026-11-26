-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_even_rank_tendsto_sharpConstant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:59:22.609625+00:00
-- url     : https://prove2.me/submissions/4532167e-ccb8-4b26-b744-04cc68b20c94

import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Definitions.Def_SharpIntermediateSubgroupBounds_Manuscript
import Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_interval_card_eq
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
import Theorems.Thm_SharpIntermediateSubgroupBounds_gaussian_even_rank_asymptotic
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
    {p : ℕ} [Fact p.Prime] :
    Tendsto (fun a : ℕ ↦
      (p : ℝ)⁻¹ ^ (a * a) *
        (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ)) atTop
      (nhds (sharpConstant (p : ℝ))) := by
  simpa only [manuscript_elementaryAbelian_interval_card_eq] using
    gaussian_even_rank_asymptotic (Fact.out : p.Prime).two_le
end SharpIntermediateSubgroupBounds
