-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.WeightedCache.zeta_euler
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:07:21.806041+00:00
-- url     : https://prove2.me/submissions/00cece97-e789-4be2-939e-41c1761446ca

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
namespace WeightedCache3SUMRefinement_e1ae71d
namespace WeightedCache
open Finset
private theorem coordinate_euler {N : ℕ} (R A : Word N) (i : Fin N) :
    (R i).val * weight (predecessor R i) A =
      ((R i).val - (A i).val : ℤ) * weight R A := by
  have hd (r a : Fin 3) :
      (r.val : ℤ) * ((r.val - 1).choose a.val : ℤ) =
        ((r.val : ℤ) - (a.val : ℤ)) * (r.val.choose a.val : ℤ) := by
    fin_cases r <;> fin_cases a <;> norm_num [Nat.choose]
  have hs (S : Word N) : weight S A = (S i).val.choose (A i).val *
      ∏ j ∈ (univ : Finset (Fin N)).erase i, ((S j).val.choose (A j).val : ℤ) :=
    (mul_prod_erase univ _ (mem_univ i)).symm
  rw [hs, hs]
  have hh : (∏ j ∈ (univ : Finset (Fin N)).erase i,
      ((predecessor R i j).val.choose (A j).val : ℤ)) =
      ∏ j ∈ (univ : Finset (Fin N)).erase i, ((R j).val.choose (A j).val : ℤ) := by
    apply prod_congr rfl
    intro j hj
    simp [predecessor, Function.update_of_ne (mem_erase.mp hj).1]
  rw [hh]
  simp only [predecessor, Function.update_self]
  rw [← mul_assoc, hd]
  ring
end WeightedCache
end WeightedCache3SUMRefinement_e1ae71d
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open WeightedCache3SUMRefinement_e1ae71d.WeightedCache
open Finset
namespace WeightedCache3SUMRefinement_e1ae71d.WeightedCache
theorem _root_.solution {N : ℕ} (f : Word N → ℤ) (h : ℕ)
    (hf : ∀ A, f A ≠ 0 → rank A = h) (R : Word N) :
    (∑ i : Fin N, (R i).val * zeta f (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * zeta f R := by
  have hh (A : Word N) : (∑ i : Fin N, (R i).val * weight (predecessor R i) A) =
      ((rank R : ℤ) - (rank A : ℤ)) * weight R A := by
    simp only [coordinate_euler, ← sum_mul, sum_sub_distrib]
    simp [rank]
  unfold zeta
  simp only [mul_sum, ← mul_assoc]
  rw [sum_comm]
  simp_rw [← sum_mul, hh]
  apply sum_congr rfl
  intro A _
  by_cases hz : f A = 0
  · simp [hz]
  · rw [hf A hz]
end WeightedCache3SUMRefinement_e1ae71d.WeightedCache
