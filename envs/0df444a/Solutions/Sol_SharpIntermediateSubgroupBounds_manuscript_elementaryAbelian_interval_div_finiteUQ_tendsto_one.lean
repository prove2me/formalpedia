-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_interval_div_finiteUQ_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:03:31.746691+00:00
-- url     : https://prove2.me/submissions/260d371b-425e-41e4-8960-ac3d8c02cea6

import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Definitions.Def_SharpIntermediateSubgroupBounds_Manuscript
import Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_bottom_index
import Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_primePowerU_eq_ratCast_finiteUQ
import Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_interval_div_primePowerU_tendsto_one
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
    {p : ℕ} [Fact p.Prime] :
    Tendsto (fun a : ℕ ↦
      (Fintype.card (elementaryAbelianInterval p (2 * a)) : ℝ) /
        (((finiteUQ
          (⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index p : ℚ) : ℝ)))
      atTop (nhds 1) := by
  apply (manuscript_elementaryAbelian_interval_div_primePowerU_tendsto_one
    (p := p)).congr'
  exact Filter.Eventually.of_forall fun a ↦ by
    dsimp only
    rw [manuscript_elementaryAbelian_bottom_index p a,
      manuscript_primePowerU_eq_ratCast_finiteUQ p (2 * a)
        (Fact.out : p.Prime).one_lt]
end SharpIntermediateSubgroupBounds
