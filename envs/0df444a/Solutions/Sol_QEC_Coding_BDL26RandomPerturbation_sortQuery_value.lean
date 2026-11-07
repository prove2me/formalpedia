-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.sortQuery_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:38:51.155041+00:00
-- url     : https://prove2.me/submissions/d94dd676-b957-4d6e-982e-d916aebb5480

import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_orderedInsertQuery_value

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {A : Type*} (cmp : A → A → Bool × ℕ)
    (r : A → A → Prop) [DecidableRel r]
    (hc : ∀ a b, (cmp a b).1 = true ↔ r a b) (L : List A) :
    (sortQuery cmp L).1 = L.insertionSort r := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [sortQuery,List.insertionSort_cons]
    rw [orderedInsertQuery_value cmp r hc,ih]
end QEC.Coding.BDL26RandomPerturbation
