-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P24.stokes_positivity_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T12:17:22.427278+00:00
-- url     : https://prove2.me/submissions/e345b7ae-26b9-4b5c-8973-1f5209a01390

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P24

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder Matrix.Norms.L2Operator

open MeasureTheory

open QAlgorithms.Papers.Independent.Intake100.P24 in
theorem solution (s0 s1 s2 s3 : ℝ)
    (hS : (stokesMatrix s0 s1 s2 s3).PosSemidef) :
    s1 ^ 2 + s2 ^ 2 + s3 ^ 2 ≤ s0 ^ 2 := by
  have e00 : stokesMatrix s0 s1 s2 s3 0 0 = ((s0 : ℂ) + s3) / 2 := by
    simp [stokesMatrix, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ,
      Matrix.one_apply, finTwoEquiv] <;> ring
  have e11 : stokesMatrix s0 s1 s2 s3 1 1 = ((s0 : ℂ) - s3) / 2 := by
    simp [stokesMatrix, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ,
      Matrix.one_apply, finTwoEquiv] <;> ring
  have e01 : stokesMatrix s0 s1 s2 s3 0 1 = ((s1 : ℂ) - s2 * Complex.I) / 2 := by
    simp [stokesMatrix, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ,
      Matrix.one_apply, finTwoEquiv] <;> ring
  have e10 : stokesMatrix s0 s1 s2 s3 1 0 = ((s1 : ℂ) + s2 * Complex.I) / 2 := by
    simp [stokesMatrix, QAlgorithms.pauliX, QAlgorithms.pauliY, QAlgorithms.pauliZ,
      Matrix.one_apply, finTwoEquiv] <;> ring
  have hdet : (stokesMatrix s0 s1 s2 s3).det
      = (((s0 ^ 2 - s1 ^ 2 - s2 ^ 2 - s3 ^ 2) / 4 : ℝ) : ℂ) := by
    rw [Matrix.det_fin_two, e00, e11, e01, e10]
    push_cast
    linear_combination (((s2 : ℂ) ^ 2) / 4) * Complex.I_sq
  have h := hS.det_nonneg
  rw [hdet, Complex.zero_le_real] at h
  nlinarith
