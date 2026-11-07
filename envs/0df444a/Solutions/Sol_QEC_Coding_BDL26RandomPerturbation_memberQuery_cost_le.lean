-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.memberQuery_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:42:19.966313+00:00
-- url     : https://prove2.me/submissions/849f4d94-9771-45f0-9b2a-504282dfac74

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Mathlib.Data.List.Dedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {A : Type*} (eq : A → A → Bool × ℕ) (C : ℕ)
    (h : ∀ a b, (eq a b).2 ≤ C) (a : A) (L : List A) :
    (memberQuery eq a L).2 ≤ L.length*(C+1) := by
  induction L with
  | nil => simp [memberQuery]
  | cons b L ih =>
    have hb := h a b
    simp only [memberQuery,List.length_cons]
    split_ifs <;> nlinarith
end QEC.Coding.BDL26RandomPerturbation
