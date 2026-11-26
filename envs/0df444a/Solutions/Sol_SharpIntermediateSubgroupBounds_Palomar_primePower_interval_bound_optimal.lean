-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.Palomar.primePower_interval_bound_optimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:05:25.538294+00:00
-- url     : https://prove2.me/submissions/2da998d3-e89d-40f8-a894-c996f3542e0f

import Definitions.Def_SharpIntermediateSubgroupBounds
import Definitions.Def_SharpIntermediateSubgroupBounds_Solution
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
import Theorems.Thm_SharpIntermediateSubgroupBounds_natFloor_indexLog
import Theorems.Thm_SharpIntermediateSubgroupBounds_primePower_interval_bound_optimal
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
theorem _root_.solution (p a : ℕ) [Fact p.Prime] :
    (∀ {G : Type*} [Group G] [Fintype G] (H : Subgroup G), H.index = p ^ a →
      Nat.card (Set.Ici H) ≤ totalQBinom p a) ∧
    Nat.card
        (Set.Ici (⊥ : Subgroup (Multiplicative (Fin a → ZMod p)))) =
      totalQBinom p a := by
  simpa only [← Nat.card_eq_fintype_card] using
    (SharpIntermediateSubgroupBounds.primePower_interval_bound_optimal p a)
end SharpIntermediateSubgroupBounds.Palomar
