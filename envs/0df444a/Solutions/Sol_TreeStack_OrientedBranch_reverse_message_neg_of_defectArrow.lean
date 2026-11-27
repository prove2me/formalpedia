-- Prove2me | solution 1 for TreeStack.OrientedBranch.reverse_message_neg_of_defectArrow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:01:18.408471+00:00
-- url     : https://prove2.me/submissions/409c94e3-b506-40c0-a48f-5f28c8bf6b75

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
import Theorems.Thm_TreeStack_OrientedBranch_defect_equations_of_both_occupied
import Theorems.Thm_TreeStack_defect_not_both_nonneg
import Theorems.Thm_TreeStack_scoreDefect_nonneg_iff
attribute [local simp] TreeStack.scoreDefect_nonneg_iff



set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (B : OrientedBranch T)
    (hArrow : B.DefectArrow C)
    (hScores : ∀ v, score T C v ≤ 0) :
    messageContribution (branchMessage C B.reverseBranch) < 0 := by
  have hEq :=
    B.defect_equations_of_both_occupied C hArrow.1.1 hArrow.1.2
  have hNotBoth :=
    defect_not_both_nonneg
      ((scoreDefect_nonneg_iff T C B.root).2 (hScores B.root))
      ((scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent))
      hEq.1 hEq.2
  apply lt_of_not_ge
  intro hReverse
  exact hNotBoth ⟨hArrow.2, hReverse⟩
end TreeStack.OrientedBranch
