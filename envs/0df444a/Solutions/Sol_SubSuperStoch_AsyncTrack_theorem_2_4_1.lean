-- Prove2me | solution 1 for SubSuperStoch.AsyncTrack.theorem_2_4_1
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-24T03:29:02.888326+00:00
-- url     : https://prove2.me/submissions/47bf8142-e19e-481c-940c-d4fd72a60a51

import Definitions.Def_SubSuperStoch_AsyncTrack_Matrix
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Lean.Elab.Tactic.Omega

open Matrix Finset SubSuperStoch.AsyncTrack

namespace D24Substochastic

lemma one_substochastic (n : ℕ) :
    IsSubStochastic (1 : Matrix (Fin n) (Fin n) ℝ) := by
  constructor
  · intro i j
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  · intro i
    change (∑ j : Fin n, if i = j then (1 : ℝ) else 0) ≤ 1
    simp

lemma mul_substochastic {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsSubStochastic A) (hB : IsSubStochastic B) : IsSubStochastic (A * B) := by
  constructor
  · intro i j
    change 0 ≤ ∑ k, A i k * B k j
    exact sum_nonneg fun k _ => mul_nonneg (hA.1 i k) (hB.1 k j)
  · intro i
    change (∑ j, ∑ k, A i k * B k j) ≤ 1
    rw [sum_comm]
    calc
      ∑ k, ∑ j, A i k * B k j = ∑ k, A i k * ∑ j, B k j := by
        simp only [mul_sum]
      _ ≤ ∑ k, A i k * 1 := by
        apply sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hB.2 k) (hA.1 i k)
      _ ≤ 1 := by simpa only [mul_one, SubSuperStoch.AsyncTrack.rowSum] using hA.2 i

lemma prodFrom_succ {n : ℕ} (F : ℕ → Matrix (Fin n) (Fin n) ℝ) (q : ℕ) :
    prodFrom F 1 (q + 1) = F (1 + q) * prodFrom F 1 q := by
  simp [prodFrom, List.range_succ, List.map_append, List.reverse_append, List.prod_append]

end D24Substochastic

theorem solution {n : ℕ} (F : ℕ → Matrix (Fin n) (Fin n) ℝ) (q : ℕ)
    (hF : ∀ s, 1 ≤ s → s ≤ q → IsSubStochastic (F s)) :
    IsSubStochastic (prodFrom F 1 q) := by
  induction q with
  | zero =>
      simpa [prodFrom] using D24Substochastic.one_substochastic n
  | succ q ih =>
      rw [D24Substochastic.prodFrom_succ]
      apply D24Substochastic.mul_substochastic
      · exact hF (1 + q) (by omega) (by omega)
      · apply ih
        intro s hs hs'
        exact hF s hs (by omega)

#print axioms solution
