-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.indexQuery_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:50:03.905396+00:00
-- url     : https://prove2.me/submissions/6dcc29d8-535d-49b7-a3b8-1d199407c315

import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {A : Type*} [DecidableEq A] (a : A) (L : List A) :
    (indexQuery a L).2 ≤ L.length := by
  induction L with
  | nil => simp [indexQuery]
  | cons b L ih =>
    by_cases h : b = a <;> simp only [indexQuery,h,if_true,if_false,List.length_cons] <;> omega
end QEC.Coding.BDL26RandomPerturbation
