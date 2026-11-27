-- Prove2me | solution 1 for TreeStack.OrientedBranch.defectArrow_tail_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:01:31.384961+00:00
-- url     : https://prove2.me/submissions/89038b56-83e7-41dc-a033-c20d94484c7b

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
import Theorems.Thm_TreeStack_OrientedBranch_defect_equations_of_both_occupied
import Theorems.Thm_TreeStack_defect_left_budget
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
    2 * scoreDefect T C B.parent ≤ scoreDefect T C B.root := by
  have hEq :=
    B.defect_equations_of_both_occupied C hArrow.1.1 hArrow.1.2
  exact
    defect_left_budget
      ((scoreDefect_nonneg_iff T C B.root).2 (hScores B.root))
      ((scoreDefect_nonneg_iff T C B.parent).2 (hScores B.parent))
      hEq.1 hEq.2 hArrow.2
end TreeStack.OrientedBranch
