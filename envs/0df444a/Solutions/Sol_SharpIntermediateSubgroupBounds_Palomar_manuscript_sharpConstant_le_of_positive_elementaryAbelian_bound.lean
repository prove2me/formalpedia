-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.Palomar.manuscript_sharpConstant_le_of_positive_elementaryAbelian_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:05:51.070999+00:00
-- url     : https://prove2.me/submissions/b41ef767-db1a-4951-a806-6c168379ea72

import Definitions.Def_SharpIntermediateSubgroupBounds
import Definitions.Def_SharpIntermediateSubgroupBounds_Solution
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
import Theorems.Thm_SharpIntermediateSubgroupBounds_manuscript_sharpConstant_le_of_positive_elementaryAbelian_bound
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
    {p : ℕ} [Fact p.Prime] {C : ℝ}
    (hC : ∀ a : ℕ, 0 < a →
      (p : ℝ)⁻¹ ^ (a * a) *
        (Nat.card (elementaryAbelianInterval p (2 * a)) : ℝ) ≤ C) :
    sharpConstant (p : ℝ) ≤ C := by
  apply SharpIntermediateSubgroupBounds.manuscript_sharpConstant_le_of_positive_elementaryAbelian_bound
    (p := p) (C := C)
  intro a ha
  simpa only [← Nat.card_eq_fintype_card] using hC a ha
end SharpIntermediateSubgroupBounds.Palomar
