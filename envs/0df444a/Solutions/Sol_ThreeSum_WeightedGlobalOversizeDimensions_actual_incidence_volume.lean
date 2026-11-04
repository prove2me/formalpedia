-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeDimensions.actual_incidence_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:25:06.593665+00:00
-- url     : https://prove2.me/submissions/221bada4-1308-4622-9bd4-b7ed20b55505

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeDimensions_partition_le_native
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeDimensions_incidence_charge_eq
import Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_outputSize_ge_sixteen
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_inflation_pos
import Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_incidence_charge_eq
import Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_prefix_dimension_bound


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalPrincipalDimensions WeightedGlobalDimensionBounds TernaryJointType
namespace ThreeSum.WeightedGlobalOversizeDimensions
theorem _root_.solution {K m n j : ℕ} (hK : 0 < K) (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) :
    (n : ℝ)*((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j) ≤
      Real.exp (incidenceSlope K m)*(n : ℝ)^WeightedGlobalOversizeRates.incidenceCharge K m := by
  have hM : 1 < outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hp : 0 < (nativePrime K m : ℝ) := by exact_mod_cast (nativePrime_prime K m).pos
  have hR : 0 < (partitionCap m : ℝ) := by unfold partitionCap; positivity
  have hS : 0 < (inflation K m : ℝ) := by exact_mod_cast inflation_pos hK m
  have hnR : (0 : ℝ) < n := by exact_mod_cast lt_trans Nat.zero_lt_one hn
  have hpR : (partitionCap m : ℝ) ≤ (nativePrime K m : ℝ) := by exact_mod_cast partition_le_native hK m
  have hslog : 0 ≤ Real.log (inflation K m : ℝ) := Real.log_nonneg (by exact_mod_cast inflation_pos hK m)
  have hplog := Real.log_le_log hR hpR
  have ha : 0 ≤ incidenceSlope K m := by unfold incidenceSlope; linarith
  have hratio := div_pos hp hR
  have hlog : Real.log (((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j)) ≤
      (j : ℝ)*incidenceSlope K m := by
    rw [Real.log_mul (pow_pos hratio _).ne' (pow_pos hS _).ne',Real.log_pow,Real.log_pow,Real.log_div hp.ne' hR.ne']
    unfold incidenceSlope
    push_cast
    nlinarith
  have hb := prefix_dimension_bound hM hn hj ha (mul_pos (pow_pos hratio _) (pow_pos hS _)).le hlog
  calc
    _ = (n : ℝ)*(((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j)) := by ring
    _ ≤ (n : ℝ)*(Real.exp (incidenceSlope K m)*(n : ℝ)^(2*incidenceSlope K m/Real.log (outputSize m : ℝ))) :=
      mul_le_mul_of_nonneg_left hb hnR.le
    _ = _ := by rw [← incidence_charge_eq hm,Real.rpow_add hnR,Real.rpow_one]; ring
end ThreeSum.WeightedGlobalOversizeDimensions
