-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeDimensions.query_slope_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:15:51.720874+00:00
-- url     : https://prove2.me/submissions/0db18e40-0ff2-426d-891a-363cb91eb122

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeDimensions_partition_le_native
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_denominator_pos
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_inflation_pos
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_analytic_admissibility


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalPrincipalDimensions WeightedGlobalDimensionBounds TernaryJointType
namespace ThreeSum.WeightedGlobalOversizeDimensions
theorem _root_.solution {K m : ℕ} (hK : 0 < K) (hm : 0 < m) : 0 ≤ querySlope K m := by
  have hR : 0 < (partitionCap m : ℝ) := by unfold partitionCap; positivity
  have hs : 0 ≤ Real.log (inflation K m : ℝ) := Real.log_nonneg (by exact_mod_cast inflation_pos hK m)
  have hpR : (partitionCap m : ℝ) ≤ (nativePrime K m : ℝ) := by exact_mod_cast partition_le_native hK m
  have hp := Real.log_le_log hR hpR
  unfold querySlope
  have hQ := mul_pos (denominator_pos hm) analytic_admissibility.2.1
  linarith
end ThreeSum.WeightedGlobalOversizeDimensions
