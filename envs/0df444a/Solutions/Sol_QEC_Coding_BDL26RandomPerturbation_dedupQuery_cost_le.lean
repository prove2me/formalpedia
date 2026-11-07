-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.dedupQuery_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:51:47.443183+00:00
-- url     : https://prove2.me/submissions/6ad35bca-9ea4-44f1-a755-f2db86fb4c85

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists
import Mathlib.Data.List.Dedup
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedDedup
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_memberQuery_cost_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_dedupQuery_value

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {A : Type*} [DecidableEq A] (eq : A → A → Bool × ℕ)
    (heq : ∀ a b, (eq a b).1 = true ↔ a = b) (C : ℕ)
    (hc : ∀ a b, (eq a b).2 ≤ C) (L : List A) :
    (dedupQuery eq L).2 ≤ (L.length+1)^2*(C+1) := by
  induction L with
  | nil => simp [dedupQuery]
  | cons a L ih =>
    have hm := memberQuery_cost_le eq C hc a (dedupQuery eq L).1
    have hlen : (dedupQuery eq L).1.length ≤ L.length := by
      rw [dedupQuery_value eq heq]
      exact (List.dedup_sublist L).length_le
    have hm' : (memberQuery eq a (dedupQuery eq L).1).2 ≤ L.length*(C+1) :=
      hm.trans (Nat.mul_le_mul_right _ hlen)
    simp only [dedupQuery,List.length_cons]
    nlinarith
end QEC.Coding.BDL26RandomPerturbation
