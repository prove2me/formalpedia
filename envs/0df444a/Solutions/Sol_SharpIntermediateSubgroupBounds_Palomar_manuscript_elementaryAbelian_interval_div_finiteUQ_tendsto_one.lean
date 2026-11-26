-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.Palomar.manuscript_elementaryAbelian_interval_div_finiteUQ_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:05:45.221586+00:00
-- url     : https://prove2.me/submissions/d27aa99f-d4ef-4b67-abc1-2ec4ba7c8ac6

import Definitions.Def_SharpIntermediateSubgroupBounds
import Definitions.Def_SharpIntermediateSubgroupBounds_Solution
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
import Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_elementaryAbelian_interval_div_finiteUQ_tendsto_one
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
    {p : ℕ} [Fact p.Prime] :
    Tendsto (fun a : ℕ ↦
      (Nat.card (elementaryAbelianInterval p (2 * a)) : ℝ) /
        (((finiteUQ
          (⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index p : ℚ) : ℝ)))
      atTop (nhds 1) := by
  simpa only [← Nat.card_eq_fintype_card] using
    (SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_interval_div_finiteUQ_tendsto_one
      (p := p))
end SharpIntermediateSubgroupBounds.Palomar
