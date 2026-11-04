-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeDimensions.actual_table_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:22:21.880613+00:00
-- url     : https://prove2.me/submissions/789af364-0b2a-4c26-85af-67f26fe5f220

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeDimensions
import Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_outputSize_ge_sixteen
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_inflation_pos
import Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_prefix_dimension_bound


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalPrincipalDimensions WeightedGlobalDimensionBounds TernaryJointType
namespace ThreeSum.WeightedGlobalOversizeDimensions
theorem _root_.solution {K m n j t : ℕ} (hK : 0 < K) (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) (ht : 0 < t) :
    (inflation K m : ℝ)^(4*j)*(t : ℝ)^j ≤ Real.exp (tableSlope K m t)*
      (n : ℝ)^(2*tableSlope K m t/Real.log (outputSize m : ℝ)) := by
  have hM : 1 < outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hS : 0 < (inflation K m : ℝ) := by exact_mod_cast inflation_pos hK m
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have hSlog : 0 ≤ Real.log (inflation K m : ℝ) := Real.log_nonneg (by exact_mod_cast inflation_pos hK m)
  have htlog : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg (by exact_mod_cast ht)
  have ha : 0 ≤ tableSlope K m t := by unfold tableSlope; positivity
  have hlog : Real.log ((inflation K m : ℝ)^(4*j)*(t : ℝ)^j) ≤ (j : ℝ)*tableSlope K m t := by
    rw [Real.log_mul (pow_pos hS _).ne' (pow_pos htR _).ne',Real.log_pow,Real.log_pow]
    unfold tableSlope
    push_cast
    nlinarith
  exact prefix_dimension_bound hM hn hj ha (mul_pos (pow_pos hS _) (pow_pos htR _)).le hlog
end ThreeSum.WeightedGlobalOversizeDimensions
