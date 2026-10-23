-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.normComparisonF
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:11:50.936342+00:00
-- url     : https://prove2.me/submissions/b06a5f41-40d7-4b35-9293-aee4301cc626

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

section x8F
open scoped Matrix.Norms.Frobenius

lemma x8_frob_eq {I : Type*} [Fintype I] (M : Matrix I I ℂ) :
    QAlgorithms.frobNorm M = Real.sqrt (Mᴴ * M).trace.re := by
  unfold QAlgorithms.frobNorm
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  norm_cast

lemma x8_ui : IsUINorm (fun A : Matrix (Fin 3) (Fin 3) ℂ => QAlgorithms.frobNorm A) := by
  refine ⟨fun A => norm_nonneg A, fun A => norm_eq_zero, fun A B => norm_add_le A B,
    fun c A => norm_smul c A, fun U V A => ?_⟩
  simp only
  have hU : (U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 U.2
  have hV : (V : Matrix (Fin 3) (Fin 3) ℂ) * (V : Matrix (Fin 3) (Fin 3) ℂ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.1 V.2
  rw [x8_frob_eq, x8_frob_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  congr 2
  calc ((V : Matrix (Fin 3) (Fin 3) ℂ)ᴴ * (Aᴴ * (U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ) *
        ((U : Matrix (Fin 3) (Fin 3) ℂ) * A * V)).trace
      = ((V : Matrix (Fin 3) (Fin 3) ℂ)ᴴ * (Aᴴ * ((U : Matrix (Fin 3) (Fin 3) ℂ)ᴴ * U) * A) * V).trace := by
        simp only [Matrix.mul_assoc]
    _ = (Aᴴ * A * (V * (V : Matrix (Fin 3) (Fin 3) ℂ)ᴴ)).trace := by
        rw [hU, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
    _ = (Aᴴ * A).trace := by rw [hV, Matrix.mul_one]

end x8F

open scoped Matrix.Norms.L2Operator

def x8A : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1, -1/2, -1/2]

lemma x8_F3 : matrixF 3 = Matrix.diagonal ![1, -1, 0] := by
  unfold matrixF; congr 1; funext i; fin_cases i <;> simp

lemma x8_spec_ge : 1 ≤ specNorm x8A := by
  unfold specNorm x8A
  rw [Matrix.l2_opNorm_diagonal]
  have := norm_le_pi_norm (![1, -1/2, -1/2] : Fin 3 → ℂ) 0
  simpa using this

lemma x8_spec_F : specNorm (matrixF 3) ≤ 1 := by
  unfold specNorm
  rw [x8_F3, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun i => ?_)
  fin_cases i <;> simp

lemma x8_frob_A : QAlgorithms.frobNorm x8A = Real.sqrt (3 / 2) := by
  rw [x8_frob_eq]; congr 1
  simp [x8A, Matrix.trace, Fin.sum_univ_three, Complex.conj_ofNat]; norm_num

lemma x8_frob_F : QAlgorithms.frobNorm (matrixF 3) = Real.sqrt 2 := by
  rw [x8_frob_eq, x8_F3]; congr 1
  simp [Matrix.trace, Fin.sum_univ_three]; norm_num

lemma x8_main : ¬ (∀ {d : ℕ} (hd : 2 ≤ d) (N : Mat d → ℝ)
    (hN : IsUINorm N) (A : Mat d) (hA : A.IsHermitian) (htrace : A.trace = 0),
    (specNorm A / specNorm (matrixF d) ≤ rescaled N A ∧
      rescaled N A ≤ traceNorm A / traceNorm (matrixF d)) ∧
    (∀ a : ℝ, 0 ≤ a →
      let B := ((a / N (matrixF d) : ℝ) : ℂ) • matrixF d
      N B = a ∧ specNorm B / specNorm (matrixF d) = rescaled N B ∧
        rescaled N B = traceNorm B / traceNorm (matrixF d))) := by
  intro h
  have hA : x8A.IsHermitian := by
    unfold x8A; rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1
    funext i; fin_cases i <;> simp [star_div₀]
  have ht : x8A.trace = 0 := by
    simp [x8A, Matrix.trace, Fin.sum_univ_three]; norm_num
  have h1 := (h (d := 3) (by norm_num) _ x8_ui x8A hA ht).1.1
  unfold rescaled at h1
  beta_reduce at h1
  rw [x8_frob_A, x8_frob_F] at h1
  have hsF : 0 < specNorm (matrixF 3) := by
    unfold specNorm; rw [x8_F3, Matrix.l2_opNorm_diagonal]
    have := norm_le_pi_norm (![1, -1, 0] : Fin 3 → ℂ) 0
    simp at this; linarith
  have h2 : 1 ≤ specNorm x8A / specNorm (matrixF 3) := by
    rw [le_div_iff₀ hsF]; linarith [x8_spec_ge, x8_spec_F]
  have h3 : Real.sqrt (3 / 2) / Real.sqrt 2 < 1 := by
    rw [div_lt_one (by positivity)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

end QAlgorithms.Papers.Independent.Gap48.P40

open scoped Matrix.Norms.L2Operator in
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P40 in
open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm) in
open QAlgorithms.Papers.Independent.Information100.P44 (Mat) in
theorem solution : ¬ (∀ {d : ℕ} (hd : 2 ≤ d) (N : Mat d → ℝ)
    (hN : IsUINorm N) (A : Mat d) (hA : A.IsHermitian) (htrace : A.trace = 0),
    (specNorm A / specNorm (matrixF d) ≤ rescaled N A ∧
      rescaled N A ≤ traceNorm A / traceNorm (matrixF d)) ∧
    (∀ a : ℝ, 0 ≤ a →
      let B := ((a / N (matrixF d) : ℝ) : ℂ) • matrixF d
      N B = a ∧ specNorm B / specNorm (matrixF d) = rescaled N B ∧
        rescaled N B = traceNorm B / traceNorm (matrixF d))) :=
  x8_main
