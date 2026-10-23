-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P41.jc_anomaly_visibility
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:28:19.434061+00:00
-- url     : https://prove2.me/submissions/3feb5128-c2f2-4e7f-814a-a7e9085d1d89

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P41

noncomputable section

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P41

namespace X6P41

lemma jc_out (eta nbar theta : ℝ) :
    jcOutput eta nbar theta = !![((1 - nbar * Real.sin theta ^ 2 : ℝ) : ℂ),
      Complex.I * ((eta * Real.sqrt (nbar * (1 - nbar)) * Real.sin theta : ℝ) : ℂ);
      -Complex.I * ((eta * Real.sqrt (nbar * (1 - nbar)) * Real.sin theta : ℝ) : ℂ),
      ((nbar * Real.sin theta ^ 2 : ℝ) : ℂ)] := by
  have hcs := Real.sin_sq_add_cos_sq theta
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [jcOutput, traceRight, Matrix.mul_apply, Fin.sum_univ_two,
      jcIsometry, fieldState, Matrix.conjTranspose_apply, -Complex.ofReal_sin, -Complex.ofReal_cos,
      Complex.ext_iff]
    try simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, or_true, and_true]
    try ring_nf
    try linear_combination (-nbar) * hcs
    try linear_combination nbar * hcs

lemma anomaly_formula (r0 b : ℝ) (h0 : r0 ≠ 0) (h1 : 1 - r0 ≠ 0) :
    outputAnomaly (!![(r0 : ℂ), Complex.I * (b : ℂ); -Complex.I * (b : ℂ), ((1 - r0 : ℝ) : ℂ)])
      (!![(r0 : ℂ), Complex.I * (b : ℂ); -Complex.I * (b : ℂ), ((1 - r0 : ℝ) : ℂ)]) =
      ((b ^ 2 / (r0 * (1 - r0)) : ℝ) : ℂ) := by
  set r1 := 1 - r0 with hr1
  set M : Matrix (Fin 2) (Fin 2) ℂ := !![(r0 : ℂ), Complex.I * (b : ℂ); -Complex.I * (b : ℂ), (r1 : ℂ)]
  have hd : Matrix.diagonal (Matrix.diag M) = Matrix.diagonal ![(r0 : ℂ), (r1 : ℂ)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [M]
  have h0' : (r0 : ℂ) ≠ 0 := by exact_mod_cast h0
  have h1' : (r1 : ℂ) ≠ 0 := by exact_mod_cast h1
  have hinv : (Matrix.diagonal ![(r0 : ℂ), (r1 : ℂ)])⁻¹ =
      Matrix.diagonal ![(r0 : ℂ)⁻¹, (r1 : ℂ)⁻¹] := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j; fin_cases i <;> fin_cases j <;> simp [h0', h1']
  unfold outputAnomaly
  rw [hd, hinv]
  have key : ((b ^ 2 / (r0 * r1) : ℝ) : ℂ) = (r0 : ℂ)⁻¹ * (b : ℂ) ^ 2 + (r1 : ℂ)⁻¹ * (b : ℂ) ^ 2 := by
    have hr1' : (r1 : ℂ) = 1 - r0 := by rw [hr1]; push_cast; ring
    have h1'' : (1 - r0 : ℂ) ≠ 0 := by rw [← hr1']; exact h1'
    push_cast
    rw [hr1']
    field_simp
    ring
  rw [key]
  simp [M, Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply, Matrix.diagonal_apply]
  ring_nf
  rw [Complex.I_sq]
  ring

end X6P41

open X6P41 in
set_option maxHeartbeats 1000000 in
theorem solution (eta nbar theta : ℝ)
    (heta : 0 ≤ eta ∧ eta ≤ 1) (hnbar : 0 < nbar ∧ nbar < 1)
    (htheta : Real.sin theta ≠ 0) :
    jcAnomaly eta nbar theta =
      ((eta ^ 2 * (1 - nbar) / (1 - nbar * Real.sin theta ^ 2) : ℝ) : ℂ) ∧
    jcAnomaly eta nbar theta =
      ((‖jcOutput eta nbar theta 0 1‖ ^ 2 /
        ((jcOutput eta nbar theta 0 0).re * (jcOutput eta nbar theta 1 1).re) : ℝ) : ℂ) := by
  have hs2 : 0 < Real.sin theta ^ 2 := by positivity
  have hs1 : Real.sin theta ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq theta, sq_nonneg (Real.cos theta)]
  have hr0 : 0 < 1 - nbar * Real.sin theta ^ 2 := by nlinarith
  have hr1 : 0 < nbar * Real.sin theta ^ 2 := by nlinarith
  have e1 : 1 - (1 - nbar * Real.sin theta ^ 2) = nbar * Real.sin theta ^ 2 := by ring
  have hA : jcAnomaly eta nbar theta =
      (((eta * Real.sqrt (nbar * (1 - nbar)) * Real.sin theta) ^ 2 /
        ((1 - nbar * Real.sin theta ^ 2) * (nbar * Real.sin theta ^ 2)) : ℝ) : ℂ) := by
    unfold jcAnomaly
    rw [jc_out]
    have := anomaly_formula (1 - nbar * Real.sin theta ^ 2)
      (eta * Real.sqrt (nbar * (1 - nbar)) * Real.sin theta) hr0.ne' (by rw [e1]; exact hr1.ne')
    rw [e1] at this
    exact this
  have hb2 : (eta * Real.sqrt (nbar * (1 - nbar)) * Real.sin theta) ^ 2 =
      eta ^ 2 * (nbar * (1 - nbar)) * Real.sin theta ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by nlinarith)]
  refine ⟨?_, ?_⟩
  · have hn : nbar ≠ 0 := hnbar.1.ne'
    rw [hA, hb2]; congr 1; field_simp
  · rw [hA, jc_out]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Complex.ofReal_re]
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
