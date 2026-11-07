-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.memberQuery_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:42:18.132195+00:00
-- url     : https://prove2.me/submissions/eeb98e3c-69e9-410a-a93e-c5e07364a6f2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Mathlib.Data.List.Dedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {A : Type*} (eq : A → A → Bool × ℕ)
    (heq : ∀ a b, (eq a b).1 = true ↔ a = b) (a : A) (L : List A) :
    (memberQuery eq a L).1 = true ↔ a ∈ L := by
  induction L with
  | nil => simp [memberQuery]
  | cons b L ih =>
    by_cases h : a = b
    · subst b
      have hb := (heq a a).mpr rfl
      simp [memberQuery,hb]
    · have hb : (eq a b).1 = false := Bool.eq_false_iff.mpr (fun ht => h ((heq a b).mp ht))
      simp [memberQuery,h,hb,ih]
end QEC.Coding.BDL26RandomPerturbation
