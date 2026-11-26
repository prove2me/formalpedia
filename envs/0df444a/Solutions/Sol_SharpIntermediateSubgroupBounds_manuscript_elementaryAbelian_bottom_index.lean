-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_bottom_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:46:29.989676+00:00
-- url     : https://prove2.me/submissions/8597e38e-a00a-48e3-9c7e-ec5cf0354ebf

import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Definitions.Def_SharpIntermediateSubgroupBounds_Manuscript
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
theorem _root_.solution (p a : ℕ)
    [Fact p.Prime] :
    (⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index = p ^ (2 * a) := by
  rw [Subgroup.index_bot]
  simp [ZMod.card]
end SharpIntermediateSubgroupBounds
