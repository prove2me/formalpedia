-- Prove2me | solution 1 for ThreeSum.TernaryPrincipalDimensions.query_dimension_expression_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:37:58.250169+00:00
-- url     : https://prove2.me/submissions/a440ec3a-bd9b-43bf-ae12-e9badab12901

import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions
import Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_prefix_dimension_bound
import Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_query_slope_pos
import Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_query_charge_eq
import Theorems.Thm_ThreeSum_TernaryCoverScale_outputSize_ge_sixteen
import Theorems.Thm_ThreeSum_TernaryDimensionBounds_near_pos
import Theorems.Thm_ThreeSum_TernaryDimensionBounds_query_log_bound
import Theorems.Thm_ThreeSum_TernaryParameters_gibbs_parameters


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPrincipalDimensions
open Real TernaryParameters TernaryEntropyRates TernaryDimensionBounds
open TernaryCoverScale TernaryLocalParameters TernaryFiniteLedger
namespace ThreeSum.TernaryPrincipalDimensions
theorem _root_.solution {m n j : ℕ} (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) (hs : primeRate m < outputRate m)
    (Q : TernaryJointType.TritWord (fixedLength (j*m)))
    (hQ : TernaryJointType.HasType Q (fixedPi (j*m))) :
    (n : ℝ)*((outputSize m : ℝ)/prime m)^j*
      (TernaryBank.nearWords Q (queryDeficit m j)).card ≤
      (Real.exp (querySlope m)/z)*(n : ℝ)^queryCharge m := by
  have hM : 1 < outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hMr : 0 < (outputSize m : ℝ) := by exact_mod_cast lt_trans Nat.zero_lt_one hM
  have hpr : 0 < (prime m : ℝ) := by exact_mod_cast (prime_prime m).pos
  have hnR : 0 < (n : ℝ) := by exact_mod_cast lt_trans Nat.zero_lt_one hn
  have hz := gibbs_parameters.2.2.1
  have hratio := div_pos hMr hpr
  have hc : 0 < ((TernaryBank.nearWords Q (queryDeficit m j)).card : ℝ) := by
    exact_mod_cast near_pos Q (queryDeficit m j)
  have hq := query_log_bound Q hQ
  have he : (fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy=
      (j : ℝ)*((fixedLength m : ℝ)*Real.log 2*queryEntropy) := by unfold fixedLength; push_cast; ring
  rw [he] at hq
  have hlog : Real.log (z*((outputSize m : ℝ)/prime m)^j*
      (TernaryBank.nearWords Q (queryDeficit m j)).card) ≤ (j : ℝ)*querySlope m := by
    rw [Real.log_mul (mul_pos hz (pow_pos hratio _)).ne' hc.ne',
      Real.log_mul hz.ne' (pow_pos hratio _).ne',Real.log_pow,Real.log_div hMr.ne' hpr.ne']
    unfold querySlope incidenceSlope
    nlinarith
  have hb := prefix_dimension_bound hM hn hj (query_slope_pos hm hs).le
    (mul_pos (mul_pos hz (pow_pos hratio _)) hc).le hlog
  calc
    _ = ((n : ℝ)/z)*(z*((outputSize m : ℝ)/prime m)^j*
      (TernaryBank.nearWords Q (queryDeficit m j)).card) := by field_simp <;> ring
    _ ≤ ((n : ℝ)/z)*(Real.exp (querySlope m)*(n : ℝ)^(2*querySlope m/Real.log (outputSize m : ℝ))) :=
      mul_le_mul_of_nonneg_left hb (div_pos hnR hz).le
    _ = _ := by
      rw [← query_charge_eq hm,Real.rpow_add hnR,Real.rpow_one]
      ring
end ThreeSum.TernaryPrincipalDimensions
