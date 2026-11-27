-- Prove2me | solution 1 for TreeStack.obstruction_not_stackable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:23:09.85842+00:00
-- url     : https://prove2.me/submissions/9f10ee79-44af-41d8-b6cc-0a6f4f1bce13

import Mathlib
import Definitions.Def_TreeStack_Estimator
import Definitions.Def_TreeStack_RootScore
import Definitions.Def_TreeStack_Obstruction
import Theorems.Thm_TreeStack_obstruction_score_eq_zero
import Theorems.Thm_TreeStack_not_stackable_iff_all_scores_nonpos


set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    (T : FiniteTree V) (r : V) :
    ¬ Stackable T.graph (obstruction T r) := by
  classical
  apply
    (not_stackable_iff_all_scores_nonpos
      T (obstruction T r)).2
  intro v
  rw [obstruction_score_eq_zero T r v]
end TreeStack
