-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.orderedInsertQuery_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:38:02.411144+00:00
-- url     : https://prove2.me/submissions/84fb0247-87f4-4985-9d18-3f11837f5121

import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {A : Type*} (cmp : A → A → Bool × ℕ)
    (r : A → A → Prop) [DecidableRel r]
    (hc : ∀ a b, (cmp a b).1 = true ↔ r a b) (a : A) (L : List A) :
    (orderedInsertQuery cmp a L).1 = L.orderedInsert r a := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    by_cases h : r a b
    · have hb : (cmp a b).1 = true := (hc a b).mpr h
      simp [orderedInsertQuery,List.orderedInsert,h,hb]
    · have hb : (cmp a b).1 = false := Bool.eq_false_iff.mpr (fun ht => h ((hc a b).mp ht))
      simp [orderedInsertQuery,List.orderedInsert,h,hb,ih]
end QEC.Coding.BDL26RandomPerturbation
