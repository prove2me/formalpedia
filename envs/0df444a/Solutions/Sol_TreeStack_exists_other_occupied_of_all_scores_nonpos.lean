-- Prove2me | solution 1 for TreeStack.exists_other_occupied_of_all_scores_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:35:18.811215+00:00
-- url     : https://prove2.me/submissions/22b6c62f-ebf6-427e-8faa-9244c034f6d1

import Mathlib
import Definitions.Def_TreeStack_Defect
import Definitions.Def_TreeStack_Support
import Theorems.Thm_TreeStack_score_eq_of_support_subset_singleton

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
namespace TreeStack
theorem _root_.solution
    {V : Type*} [Fintype V]
    (T : FiniteTree V) (C : Configuration V)
    (hScores : ∀ v, score T C v ≤ 0)
    {r : V} (hr : 0 < C r) :
    ∃ v, v ≠ r ∧ 0 < C v := by
  by_contra hOther
  have hSupport : ∀ v, 0 < C v → v = r := by
    intro v hv
    by_contra hvr
    exact hOther ⟨v, hvr, hv⟩
  have hEq := score_eq_of_support_subset_singleton T C r hSupport
  have hPos : 0 < score T C r := by
    rw [hEq]
    exact_mod_cast hr
  exact (not_lt_of_ge (hScores r)) hPos
end TreeStack
