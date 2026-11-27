-- Prove2me | solution 1 for TreeStack.OrientedBranch.not_defectArrow_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:03:44.348269+00:00
-- url     : https://prove2.me/submissions/2e23faca-6f85-481a-ba1a-faa2b398f82c

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
import Theorems.Thm_TreeStack_OrientedBranch_reverse_message_neg_of_defectArrow

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
    ¬ B.reverseBranch.DefectArrow C := by
  intro hReverse
  exact
    (not_lt_of_ge hReverse.2)
      (B.reverse_message_neg_of_defectArrow C hArrow hScores)
end TreeStack.OrientedBranch
