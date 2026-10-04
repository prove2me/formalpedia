-- Prove2me | solution 1 for ResourceScheduling.Graph.q2_res11_stronglyNPHard
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T06:53:44.101327+00:00
-- url     : https://prove2.me/submissions/99851489-d054-4c27-8eeb-ffa2c2d6c11a

import Theorems.Thm_ResourceScheduling_Graph_reduceWord_correct
import Theorems.Thm_ResourceScheduling_Graph_reduceWord_polyTime
import Theorems.Thm_CookPvsNP_polyReducible_trans

set_option autoImplicit false

open CookPvsNP ResourceScheduling.Graph

-- CONDITIONAL SKETCH: the time bound and transitivity are tracked Open dependencies.
theorem solution (hP : NPHard pathsLang) : StronglyNPHard Q2Yes encQ2 := by
  change NPHard (codeLang Q2Yes encQ2)
  intro Sym _ _ L hL
  exact polyReducible_trans (hP Sym L hL)
    ⟨reduceWord, reduceWord_polyTime, fun w => (reduceWord_correct w).1⟩

#print axioms solution
