-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.dedupQuery_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:43:02.559481+00:00
-- url     : https://prove2.me/submissions/79d45659-7b84-4bf9-a0b9-89998ffb6594

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Mathlib.Data.List.Dedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_memberQuery_correct

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {A : Type*} [DecidableEq A] (eq : A → A → Bool × ℕ)
    (heq : ∀ a b, (eq a b).1 = true ↔ a = b) (L : List A) :
    (dedupQuery eq L).1 = L.dedup := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have h : (memberQuery eq a (dedupQuery eq L).1).1 = true ↔ a ∈ L := by
      rw [memberQuery_correct eq heq,ih,List.mem_dedup]
    by_cases ha : a ∈ L
    · have hq := h.mpr ha
      simp only [dedupQuery]
      rw [if_pos hq]
      simpa only [List.dedup_cons_of_mem ha] using ih
    · have hq : (memberQuery eq a (dedupQuery eq L).1).1 = false :=
        Bool.eq_false_iff.mpr (fun ht => ha (h.mp ht))
      have hn : (memberQuery eq a (dedupQuery eq L).1).1 ≠ true := by rw [hq]; decide
      simp only [dedupQuery]
      rw [if_neg hn]
      simpa only [List.dedup_cons_of_notMem ha] using congrArg (List.cons a) ih
end QEC.Coding.BDL26RandomPerturbation
