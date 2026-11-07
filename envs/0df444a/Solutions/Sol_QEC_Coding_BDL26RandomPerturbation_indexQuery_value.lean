-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.indexQuery_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:50:02.600209+00:00
-- url     : https://prove2.me/submissions/88e50727-5222-45cb-b406-7173c98aca6a

import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {A : Type*} [DecidableEq A] [BEq A] [LawfulBEq A] (a : A) (L : List A) :
    (indexQuery a L).1 = L.idxOf a := by
  induction L with
  | nil => simp [indexQuery]
  | cons b L ih =>
    by_cases h : b = a
    · simp [indexQuery,h]
    · simp [indexQuery,h,List.idxOf_cons_ne L h,ih]
end QEC.Coding.BDL26RandomPerturbation
