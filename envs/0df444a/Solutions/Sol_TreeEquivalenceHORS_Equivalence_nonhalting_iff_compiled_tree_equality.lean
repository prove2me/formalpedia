-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.nonhalting_iff_compiled_tree_equality
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T18:17:42.572362+00:00
-- url     : https://prove2.me/submissions/b231f129-1eb5-4f47-979a-c95157ab10b3

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Compiler
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_theorem_5_8
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_productive_tree_eq_iff_observations

namespace TreeEquivalenceHORS.Equivalence


private theorem proved_here (M : Machine) :
    ¬ M.Halts ↔ (compile .L M).BT = (compile .R M).BT := by
  obtain ⟨_, hs, hd⟩ := theorem_5_8
  obtain ⟨vl, _, pl, al, _⟩ := hs M .L
  obtain ⟨vr, _, pr, ar, _⟩ := hs M .R
  rw [productive_tree_eq_iff_observations vl vr (al.trans ar.symm) pl pr, hd M, al, ar]
  constructor
  · intro hn w a b ha hb hl hr
    by_contra hne
    exact hn ⟨w, a, b, ha, hb, hne, hl, hr⟩
  · rintro agree ⟨w, a, b, ha, hb, hne, hl, hr⟩
    exact hne (agree w a b ha hb hl hr)

end TreeEquivalenceHORS.Equivalence

open TreeEquivalenceHORS.Equivalence

theorem solution (M : Machine) :
    ¬ M.Halts ↔ (compile .L M).BT = (compile .R M).BT := proved_here M
