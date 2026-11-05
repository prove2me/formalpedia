-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeDimensions.query_slope_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:20:08.217035+00:00
-- url     : https://prove2.me/submissions/8b5c060a-cb3a-4a38-af6a-d563dbe6600a

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeDimensions
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeDimensions_partition_le_native
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalEntropyRates_denominator_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizePrime_inflation_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_analytic_admissibility


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalPrincipalDimensions WeightedGlobalDimensionBounds TernaryJointType
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeDimensions
theorem _root_.solution {K m : ℕ} (hK : 0 < K) (hm : 0 < m) : 0 ≤ querySlope K m := by
  have hR : 0 < (partitionCap m : ℝ) := by unfold partitionCap; positivity
  have hs : 0 ≤ Real.log (inflation K m : ℝ) := Real.log_nonneg (by exact_mod_cast inflation_pos hK m)
  have hpR : (partitionCap m : ℝ) ≤ (nativePrime K m : ℝ) := by exact_mod_cast partition_le_native hK m
  have hp := Real.log_le_log hR hpR
  unfold querySlope
  have hQ := mul_pos (denominator_pos hm) analytic_admissibility.2.1
  linarith
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeDimensions
