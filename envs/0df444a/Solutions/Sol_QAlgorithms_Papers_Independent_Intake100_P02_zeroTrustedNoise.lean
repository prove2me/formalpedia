-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P02.zeroTrustedNoise
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-31T00:27:00.667065+00:00
-- url     : https://prove2.me/submissions/89058578-0e9e-4231-90b2-4a7e7fb24822

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P02

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Intake100.P02

theorem solution (eta omega : ℝ)
    (heta_positive : 0 < eta) (heta_lt_one : eta < 1)
    (homega : 1 / 2 ≤ omega) :
    siftedRateExpression eta omega 0 = reverseRateExpression eta omega / 2 := by
  have hw : omega ≠ 0 := by linarith
  have he : 1 - eta ≠ 0 := by linarith
  have hv : conditionalSymplecticEigenvalue eta omega 0 = 1 / 2 := by
    unfold conditionalSymplecticEigenvalue
    simp only [mul_zero, zero_mul, add_zero, mul_one]
    have hrad : omega / (4 * omega) = (1 / 2 : ℝ) ^ 2 := by
      field_simp
      <;> ring
    rw [hrad, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hh : varianceEntropy (1 / 2) = 0 := by
    norm_num [varianceEntropy, Real.logb]
  have hf : omega / ((1 - eta) * ((1 - eta) * omega)) = ((1 - eta) ^ 2)⁻¹ := by
    field_simp
    <;> ring
  rw [siftedRateExpression, hv, hh, reverseRateExpression]
  simp only [mul_zero, zero_mul, add_zero]
  rw [hf, Real.logb_inv, Real.logb_pow]
  ring

#print axioms solution
