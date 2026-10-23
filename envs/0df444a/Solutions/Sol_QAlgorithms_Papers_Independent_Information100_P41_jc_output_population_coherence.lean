-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P41.jc_output_population_coherence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:25:03.39623+00:00
-- url     : https://prove2.me/submissions/a96932de-7911-409f-bb47-f71d01afcde3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P41

noncomputable section

open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P41

lemma x6_jc11 (eta nbar theta : ℝ) :
    jcOutput eta nbar theta 1 1 = ((nbar * Real.sin theta ^ 2 : ℝ) : ℂ) := by
  simp [jcOutput, traceRight, Matrix.mul_apply, Fin.sum_univ_two,
    jcIsometry, fieldState, Matrix.conjTranspose_apply, -Complex.ofReal_sin, -Complex.ofReal_cos]
  push_cast
  ring_nf
  try simp [Complex.ext_iff]
  try ring

lemma x6_jc01 (eta nbar theta : ℝ) :
    jcOutput eta nbar theta 0 1 =
      Complex.I * ((eta * Real.sqrt (nbar * (1 - nbar)) * Real.sin theta : ℝ) : ℂ) := by
  simp [jcOutput, traceRight, Matrix.mul_apply, Fin.sum_univ_two,
    jcIsometry, fieldState, Matrix.conjTranspose_apply, -Complex.ofReal_sin, -Complex.ofReal_cos]
  push_cast
  ring_nf
  try simp [Complex.ext_iff]
  try ring

theorem solution (eta nbar theta : ℝ)
    (heta : 0 ≤ eta ∧ eta ≤ 1) (hnbar : 0 ≤ nbar ∧ nbar ≤ 1)
    (htheta : 0 ≤ theta ∧ theta ≤ Real.pi / 2) :
    (jcOutput eta nbar theta 1 1).re = nbar * Real.sin theta ^ 2 ∧
    ‖jcOutput eta nbar theta 0 1‖ = eta * Real.sqrt (nbar * (1 - nbar)) * Real.sin theta := by
  refine ⟨by rw [x6_jc11, Complex.ofReal_re], ?_⟩
  rw [x6_jc01, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg]
  have hs : 0 ≤ Real.sin theta :=
    Real.sin_nonneg_of_nonneg_of_le_pi htheta.1 (by linarith [htheta.2, Real.pi_pos])
  have := Real.sqrt_nonneg (nbar * (1 - nbar))
  have := heta.1
  positivity
