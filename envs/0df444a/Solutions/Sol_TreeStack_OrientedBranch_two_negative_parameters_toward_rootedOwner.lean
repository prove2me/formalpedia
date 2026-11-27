-- Prove2me | solution 1 for TreeStack.OrientedBranch.two_negative_parameters_toward_rootedOwner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:09:53.011604+00:00
-- url     : https://prove2.me/submissions/6988ac36-4d41-49dd-b877-487bae7c0d2f

import Mathlib
import Definitions.Def_TreeStack_DefectCharge
import Definitions.Def_TreeStack_Auxiliary
import Theorems.Thm_TreeStack_OrientedBranch_defect_equations_of_both_occupied
import Theorems.Thm_TreeStack_defect_two_negative
import Theorems.Thm_TreeStack_scoreDefect_nonneg_iff
attribute [local simp] TreeStack.scoreDefect_nonneg_iff



set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V) (B : OrientedBranch T)
    (hEdge : B.SupportEdge C)
    (hScores : ∀ v, score T C v ≤ 0)
    (haNeg :
      messageContribution (branchMessage C B) < 0)
    (hbNeg :
      messageContribution (branchMessage C B.reverseBranch) < 0)
    (hOwner : B.parent = B.rootedOwner ambientRoot) :
    ∃ r q : ℤ,
      0 ≤ r ∧ 0 ≤ q ∧
      messageContribution (branchMessage C B) = -(2 * r + 1) ∧
      messageContribution (branchMessage C B.reverseBranch) = -(2 * q + 1) ∧
      scoreDefect T C B.root = r + 2 * q ∧
      scoreDefect T C (B.rootedOwner ambientRoot) = q + 2 * r := by
  have hEq :=
    B.defect_equations_of_both_occupied C hEdge.1 hEdge.2
  rcases
      defect_two_negative
        ((scoreDefect_nonneg_iff T C B.root).2 (hScores B.root))
        ((scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent))
        hEq.1 hEq.2 haNeg hbNeg with
    ⟨r, q, hr, hq, ha, hb, hRoot, hParent⟩
  refine ⟨r, q, hr, hq, ha, hb, hRoot, ?_⟩
  rw [← hOwner]
  exact hParent
end TreeStack.OrientedBranch
