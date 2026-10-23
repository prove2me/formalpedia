-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.secondOrderComposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:25:09.027959+00:00
-- url     : https://prove2.me/submissions/2db1db02-70ba-4521-83db-ae73db3ccabf

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Information100.P37

lemma X7S_resp_kron {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ) :
    response (Matrix.kronecker U V) =
      1 - Matrix.kronecker (1 - response U) (1 - response V) := by
  have ht : transition (Matrix.kronecker U V) =
      Matrix.kronecker (transition U) (transition V) := by
    ext ⟨a, b⟩ ⟨a', b'⟩
    simp [transition, Matrix.kronecker, Matrix.kroneckerMap_apply, Complex.normSq_mul]
  simp only [response, sub_sub_cancel, ht]
  simp only [Matrix.kronecker]
  rw [← Matrix.kroneckerMap_transpose, ← Matrix.mul_kronecker_mul]

end QAlgorithms.Papers.Independent.Information100.P37

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P37 in
theorem solution {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Nonempty ι] [Nonempty κ] (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hV : V ∈ Matrix.unitaryGroup κ ℂ) :
    let m := (Fintype.card ι : ℝ)
    let n := (Fintype.card κ : ℝ)
    let A := response U
    let B := response V
    let G := response (Matrix.kronecker U V)
    G.trace = m * n - (m - A.trace) * (n - B.trace) ∧
    (G * G).trace = m * n - 2 * (m - A.trace) * (n - B.trace) +
      (m - 2 * A.trace + (A * A).trace) * (n - 2 * B.trace + (B * B).trace) ∧
    diagonalSq G = n * diagonalSq A + m * diagonalSq B + diagonalSq A * diagonalSq B +
      2 * A.trace * B.trace - 2 * diagonalSq A * B.trace - 2 * A.trace * diagonalSq B := by
  intro m n A B G
  have hG : G = 1 - Matrix.kroneckerMap (· * ·) (1 - A) (1 - B) := by
    have := X7S_resp_kron U V
    simp only [Matrix.kronecker] at this
    exact this
  have h1 : ((1 : Matrix (ι × κ) (ι × κ) ℝ)).trace = m * n := by
    simp [m, n, Matrix.trace_one, Fintype.card_prod]
  have hA1 : (1 - A).trace = m - A.trace := by simp [Matrix.trace_sub, m]
  have hB1 : (1 - B).trace = n - B.trace := by simp [Matrix.trace_sub, n]
  have hA2 : ((1 - A) * (1 - A)).trace = m - 2 * A.trace + (A * A).trace := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, Matrix.trace_sub, Matrix.trace_one, m]; ring
  have hB2 : ((1 - B) * (1 - B)).trace = n - 2 * B.trace + (B * B).trace := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, Matrix.trace_sub, Matrix.trace_one, n]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hG, Matrix.trace_sub, h1, Matrix.trace_kronecker, hA1, hB1]
  · rw [hG, sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, ← Matrix.mul_kronecker_mul,
      Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, h1, Matrix.trace_kronecker,
      Matrix.trace_kronecker, hA1, hB1, hA2, hB2]
    ring
  · have hd : ∀ a b, G (a, b) (a, b) = A a a + B b b - A a a * B b b := by
      intro a b
      rw [hG]
      simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sub_apply]
      ring
    simp only [diagonalSq, Fintype.sum_prod_type, hd, Matrix.trace]
    have e : ∀ a b, (A a a + B b b - A a a * B b b) ^ 2 =
        A a a ^ 2 + B b b ^ 2 + A a a ^ 2 * B b b ^ 2 + 2 * (A a a * B b b)
          - 2 * (A a a ^ 2 * B b b) - 2 * (A a a * B b b ^ 2) := by intro a b; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Matrix.diag, m, n]
    ring
