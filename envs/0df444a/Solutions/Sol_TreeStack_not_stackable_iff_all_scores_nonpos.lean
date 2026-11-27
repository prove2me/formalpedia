-- Prove2me | solution 1 for TreeStack.not_stackable_iff_all_scores_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:02:24.601914+00:00
-- url     : https://prove2.me/submissions/65c570f1-d05e-48b7-9b17-94fd336ab9b6

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
import Theorems.Thm_TreeStack_stackableAt_iff_score_pos

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) :
    ¬ Stackable T.graph C ↔ ∀ r : V, score T C r ≤ 0 := by
  rw [Stackable]
  push_neg
  constructor
  · intro h r
    have hn : ¬ 0 < score T C r := by
      intro hp
      exact h r ((stackableAt_iff_score_pos T C r).2 hp)
    omega
  · intro h r hs
    have hp := (stackableAt_iff_score_pos T C r).1 hs
    have hn := h r
    omega
end TreeStack
