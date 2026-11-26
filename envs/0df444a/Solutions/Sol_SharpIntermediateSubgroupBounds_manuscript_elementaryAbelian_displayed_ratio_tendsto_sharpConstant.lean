-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_displayed_ratio_tendsto_sharpConstant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:02:04.293008+00:00
-- url     : https://prove2.me/submissions/d39cb1c3-a9e3-4875-bf87-83a4ddb41fcd

import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Definitions.Def_SharpIntermediateSubgroupBounds_Manuscript
import Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_indexLog_rpow_eq
import Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_even_rank_tendsto_sharpConstant
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
        (((⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index : ℝ) ^
          (indexLog p
            (⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index / 4)))
      atTop (nhds (sharpConstant (p : ℝ))) := by
  apply (manuscript_elementaryAbelian_even_rank_tendsto_sharpConstant
    (p := p)).congr'
  exact Filter.Eventually.of_forall fun a ↦ by
    dsimp only
    rw [manuscript_elementaryAbelian_indexLog_rpow_eq p a]
    simp only [div_eq_mul_inv, inv_pow]
    ring
end SharpIntermediateSubgroupBounds
