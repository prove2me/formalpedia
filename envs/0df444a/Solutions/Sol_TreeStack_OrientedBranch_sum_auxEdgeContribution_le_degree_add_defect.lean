-- Prove2me | solution 1 for TreeStack.OrientedBranch.sum_auxEdgeContribution_le_degree_add_defect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:34:21.508584+00:00
-- url     : https://prove2.me/submissions/c0ea31f6-4875-4d4f-9de6-321c5d3deef7

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
import Definitions.Def_TreeStack_GlobalCharge
import Theorems.Thm_TreeStack_OrientedBranch_sum_edgeSeparatedCharge_le_auxDefectBudget
import Theorems.Thm_TreeStack_OrientedBranch_edgeContribution_le_endpoint_add_separated_charge
import Theorems.Thm_TreeStack_OrientedBranch_sum_edgeEndpointWeight_eq_auxDegreePotential

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
set_option maxHeartbeats 800000
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (hRootPos : 0 < C ambientRoot)
    (hScores : ∀ v, score T C v ≤ 0) :
    (∑ e : T.graph.edgeFinset,
      auxEdgeContribution C ambientRoot hScores (edgeBranch e)) ≤
      auxDegreePotential C ambientRoot hScores +
        auxDefectBudget C ambientRoot hScores := by
  have hLocal :
      (∑ e : T.graph.edgeFinset,
        auxEdgeContribution C ambientRoot hScores (edgeBranch e)) ≤
        ∑ e : T.graph.edgeFinset,
          ((auxWeightInt C ambientRoot hScores (edgeBranch e).root +
              auxWeightInt C ambientRoot hScores (edgeBranch e).parent) +
            edgeSeparatedCharge C ambientRoot hScores e) := by
    exact Finset.sum_le_sum fun e _ =>
      edgeContribution_le_endpoint_add_separated_charge
        C ambientRoot hRootPos hScores e
  rw [Finset.sum_add_distrib,
    sum_edgeEndpointWeight_eq_auxDegreePotential] at hLocal
  exact hLocal.trans (add_le_add (le_refl _)
    (sum_edgeSeparatedCharge_le_auxDefectBudget
      C ambientRoot hScores))
end TreeStack.OrientedBranch
