-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P03.noTrustedNoise
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T12:57:52.211979+00:00
-- url     : https://prove2.me/submissions/eaabc516-4e59-44e7-876d-a95856030918

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P03
noncomputable section

open QAlgorithms.Papers.Independent.Bridge50.P03

theorem solution (eta omega gamma : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (homega : 1 ≤ omega)
    (hgamma : 1 ≤ gamma) :
    signedDetectorRate eta omega 1 gamma =
      -Real.logb 2 (1 - eta) - thermalVarianceEntropy omega := by
  have he : 0 < 1 - eta := by linarith
  have ho : 0 < omega := by linarith
  have hA : (1 * omega + (1 - 1) * (1 - eta) * gamma) /
        ((1 - eta) * (1 * (1 - eta) * omega + (1 - 1) * gamma)) = ((1 - eta) ^ 2)⁻¹ := by
    simp only [sub_self, zero_mul, add_zero, one_mul, mul_zero, mul_one]
    field_simp
  have hB : (omega * (1 + (1 - eta) * (1 - 1) * omega * gamma)) /
        (1 * omega + (1 - eta) * (1 - 1) * gamma) = 1 := by
    simp only [sub_self, zero_mul, add_zero, one_mul, mul_zero, mul_one]
    field_simp
  have hT : thermalVarianceEntropy 1 = 0 := by
    norm_num [thermalVarianceEntropy, Real.logb]
  unfold signedDetectorRate
  rw [if_neg one_ne_zero, hA, hB, Real.sqrt_one, hT, Real.logb_inv, Real.logb_pow]
  push_cast
  ring

end
