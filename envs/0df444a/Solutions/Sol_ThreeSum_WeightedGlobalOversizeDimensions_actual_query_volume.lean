-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeDimensions.actual_query_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:29:15.811207+00:00
-- url     : https://prove2.me/submissions/cba73fdb-5617-49d2-900d-36bdaa0460b2

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeDimensions_query_charge_eq
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeDimensions_query_slope_nonneg
import Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_outputSize_ge_sixteen
import Theorems.Thm_ThreeSum_WeightedGlobalDimensionBounds_near_pos
import Theorems.Thm_ThreeSum_WeightedGlobalDimensionBounds_query_log_bound
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_inflation_pos
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_gibbs_parameters
import Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_prefix_dimension_bound
import Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_query_charge_eq


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalPrincipalDimensions WeightedGlobalDimensionBounds TernaryJointType
namespace ThreeSum.WeightedGlobalOversizeDimensions
theorem _root_.solution {K m n j : ℕ} (hK : 0 < K) (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) (Q : TritWord (fixedLength (j*m)))
    (hQ : HasType Q (fixedPi (j*m))) :
    (n : ℝ)*((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j)*
      (WeightedGlobalBank.nearWords Q (queryDeficit m j)).card ≤
      (Real.exp (querySlope K m)/z^1024)*(n : ℝ)^WeightedGlobalOversizeRates.queryCharge K m := by
  have hM : 1 < outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hp : 0 < (nativePrime K m : ℝ) := by exact_mod_cast (nativePrime_prime K m).pos
  have hR : 0 < (partitionCap m : ℝ) := by unfold partitionCap; positivity
  have hS : 0 < (inflation K m : ℝ) := by exact_mod_cast inflation_pos hK m
  have hnR : (0 : ℝ) < n := by exact_mod_cast lt_trans Nat.zero_lt_one hn
  have hz := pow_pos gibbs_parameters.2.2.1 1024
  have hratio := div_pos hp hR
  have hc : 0 < ((WeightedGlobalBank.nearWords Q (queryDeficit m j)).card : ℝ) := by exact_mod_cast near_pos Q _
  have hq := query_log_bound Q hQ
  have he : (fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy=
      (j : ℝ)*((fixedLength m : ℝ)*Real.log 2*queryEntropy) := by unfold fixedLength; push_cast; ring
  rw [he] at hq
  have hlog : Real.log (z^1024*((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j)*
      (WeightedGlobalBank.nearWords Q (queryDeficit m j)).card) ≤ (j : ℝ)*querySlope K m := by
    rw [Real.log_mul (mul_pos (mul_pos hz (pow_pos hratio _)) (pow_pos hS _)).ne' hc.ne',
      Real.log_mul (mul_pos hz (pow_pos hratio _)).ne' (pow_pos hS _).ne',
      Real.log_mul hz.ne' (pow_pos hratio _).ne',Real.log_pow,Real.log_pow,Real.log_pow,Real.log_div hp.ne' hR.ne']
    unfold querySlope
    push_cast
    nlinarith
  have hb := prefix_dimension_bound hM hn hj (query_slope_nonneg hK hm)
    (mul_pos (mul_pos (mul_pos hz (pow_pos hratio _)) (pow_pos hS _)) hc).le hlog
  calc
    _ = ((n : ℝ)/z^1024)*(z^1024*((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j)*
      (WeightedGlobalBank.nearWords Q (queryDeficit m j)).card) := by field_simp [gibbs_parameters.2.2.1.ne'] <;> ring
    _ ≤ ((n : ℝ)/z^1024)*(Real.exp (querySlope K m)*(n : ℝ)^(2*querySlope K m/Real.log (outputSize m : ℝ))) :=
      mul_le_mul_of_nonneg_left hb (div_pos hnR hz).le
    _ = _ := by rw [← query_charge_eq hm,Real.rpow_add hnR,Real.rpow_one]; ring
end ThreeSum.WeightedGlobalOversizeDimensions
