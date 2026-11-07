-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.sortQuery_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:50:09.887455+00:00
-- url     : https://prove2.me/submissions/af042490-61b0-4108-935c-b8b7450c2667

import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_sortQuery_value
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_orderedInsertQuery_cost_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {A : Type*} (cmp : A → A → Bool × ℕ)
    (r : A → A → Prop) [DecidableRel r]
    (hv : ∀ a b, (cmp a b).1 = true ↔ r a b) (C : ℕ)
    (hc : ∀ a b, (cmp a b).2 ≤ C) (L : List A) :
    (sortQuery cmp L).2 ≤ (L.length+1)^2*(C+1) := by
  induction L with
  | nil => simp [sortQuery]
  | cons a L ih =>
    have hi := orderedInsertQuery_cost_le cmp C hc a (sortQuery cmp L).1
    have hlen : ((sortQuery cmp L).1).length = L.length := by
      rw [sortQuery_value cmp r hv,List.length_insertionSort]
    rw [hlen] at hi
    simp only [sortQuery,List.length_cons]
    nlinarith
end QEC.Coding.BDL26RandomPerturbation
