-- Prove2me | solution 1 for TreeStack.OrientedBranch.sum_edgeSeparatedCharge_le_auxDefectBudget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:29:17.521766+00:00
-- url     : https://prove2.me/submissions/a0a86bb3-3f1f-447e-898b-889a5c733da8

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
import Definitions.Def_TreeStack_GlobalCharge
import Theorems.Thm_TreeStack_OrientedBranch_sum_edgeOwner_charge_le_auxDefectBudget
import Theorems.Thm_TreeStack_OrientedBranch_edgeSeparatedCharge_le_owner_charge

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    (∑ e : T.graph.edgeFinset,
      edgeSeparatedCharge C ambientRoot hScores e) ≤
      auxDefectBudget C ambientRoot hScores := by
  calc
    (∑ e : T.graph.edgeFinset,
        edgeSeparatedCharge C ambientRoot hScores e) ≤
        ∑ e : T.graph.edgeFinset,
          auxWeightInt C ambientRoot hScores (edgeOwner ambientRoot e) *
            scoreDefect T C (edgeOwner ambientRoot e) := by
      exact Finset.sum_le_sum fun e _ =>
        edgeSeparatedCharge_le_owner_charge C ambientRoot hScores e
    _ ≤ auxDefectBudget C ambientRoot hScores :=
      sum_edgeOwner_charge_le_auxDefectBudget C ambientRoot hScores
end TreeStack.OrientedBranch
