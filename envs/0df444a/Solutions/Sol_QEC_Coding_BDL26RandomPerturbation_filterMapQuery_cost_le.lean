-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.filterMapQuery_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:51:56.470329+00:00
-- url     : https://prove2.me/submissions/b27876ec-12d2-46af-91c3-931530fd4477

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedFilterMap

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {A B : Type*} (q : A → Option B × ℕ) (L : List A) (C : ℕ)
    (hq : ∀ a ∈ L, (q a).2 ≤ C) : (filterMapQuery q L).2 ≤ L.length*(C+1) := by
  induction L with
  | nil => simp [filterMapQuery]
  | cons a L ih =>
    have ha := hq a (by simp)
    have ht := ih (fun b hb => hq b (by simp [hb]))
    simp only [filterMapQuery,List.length_cons]
    nlinarith
end QEC.Coding.BDL26RandomPerturbation
