-- Prove2me | solution 1 for TreeStack.stackableAt_iff_score_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:01:28.102882+00:00
-- url     : https://prove2.me/submissions/aa348ccc-8815-4780-99a8-07710cac3514

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
import Theorems.Thm_TreeStack_stackableAt_of_score_pos
import Theorems.Thm_TreeStack_score_pos_of_stackableAt

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) (r : V) :
    StackableAt T.graph C r ↔ 0 < score T C r := by
  constructor
  · exact score_pos_of_stackableAt T C r
  · exact stackableAt_of_score_pos T C r
end TreeStack
