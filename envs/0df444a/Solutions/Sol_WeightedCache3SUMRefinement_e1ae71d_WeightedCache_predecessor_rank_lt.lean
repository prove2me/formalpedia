-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.WeightedCache.predecessor_rank_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:06:26.826345+00:00
-- url     : https://prove2.me/submissions/e9cad79e-fcfe-41ed-a0d8-081e4f45c438

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open WeightedCache3SUMRefinement_e1ae71d.WeightedCache
open Finset
namespace WeightedCache3SUMRefinement_e1ae71d.WeightedCache
theorem _root_.solution {N : ℕ} (R : Word N) (i : Fin N)
    (hi : 0 < (R i).val) : rank (predecessor R i) < rank R := by
  unfold rank predecessor
  rw [← add_sum_erase univ _ (mem_univ i), ← add_sum_erase univ _ (mem_univ i)]
  have hh : (∑ j ∈ (univ : Finset (Fin N)).erase i,
      (Function.update R i ⟨(R i).val - 1, by omega⟩ j).val) =
      ∑ j ∈ (univ : Finset (Fin N)).erase i, (R j).val := by
    apply sum_congr rfl
    intro j hj
    simp [Function.update_of_ne (mem_erase.mp hj).1]
  rw [hh]
  simp only [Function.update_self]
  omega
end WeightedCache3SUMRefinement_e1ae71d.WeightedCache
