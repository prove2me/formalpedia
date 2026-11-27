-- Prove2me | solution 1 for TreeStack.OrientedBranch.defectEdgeState_of_supportEdge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:34:36.467652+00:00
-- url     : https://prove2.me/submissions/722f46a5-6ce9-4af3-a0f3-3504d19b2e6c

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
import Theorems.Thm_TreeStack_OrientedBranch_defectEdgeState_of_scores_nonpos


set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C)
    (hScores : ∀ v, score T C v ≤ 0) :
    DefectEdgeState
      (messageContribution (branchMessage C B))
      (messageContribution (branchMessage C B.reverseBranch))
      (scoreDefect T C B.root)
      (scoreDefect T C B.parent) := by
  exact B.defectEdgeState_of_scores_nonpos C
    hEdge.1 hEdge.2 (hScores B.root) (hScores B.parent)
end TreeStack.OrientedBranch
