-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeOverhead.base_factor_prefix_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:41:03.456388+00:00
-- url     : https://prove2.me/submissions/ad7a58ef-42ca-49dd-93d5-e847dcd77610

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeRates
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeOverhead
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeOverhead_baseFactor_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizeOverhead_baseFactor_rate_bound
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverScale_outputSize_ge_sixteen
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalEntropyRates_denominator_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_log_two_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPrincipalDimensions_output_log_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPrincipalDimensions_prefix_dimension_bound


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeOverhead
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
open scoped Topology
set_option maxHeartbeats 1000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeOverhead
theorem _root_.solution {K k m n j : ℕ} (hK : 0 < K) (hk : 0 < k)
    (hm : 0 < m) (hn : 1 < n) (hj : j ≤ radixLength m n) (c d : ℕ) :
    (baseFactor K k c d m : ℝ)^j ≤ (baseFactor K k c d m : ℝ)*(n : ℝ)^overheadCharge k c d m := by
  have hM : 1 < outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hB := baseFactor_pos K k c d m
  have hBr : 0 < (baseFactor K k c d m : ℝ) := by exact_mod_cast hB
  have ha : 0 ≤ Real.log (baseFactor K k c d m : ℝ) := Real.log_nonneg (by exact_mod_cast hB)
  have hb := WeightedGlobalPrincipalDimensions.prefix_dimension_bound hM hn hj ha
    (pow_pos hBr _).le (by rw [Real.log_pow] : Real.log ((baseFactor K k c d m : ℝ)^j) ≤
      (j : ℝ)*Real.log (baseFactor K k c d m : ℝ))
  rw [Real.exp_log hBr] at hb
  have hRate := baseFactor_rate_bound hK hk hm c d
  have hln := (div_le_iff₀ (denominator_pos hm)).mp hRate
  have he := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hln (by norm_num : (0 : ℝ) ≤ 2))
    (WeightedGlobalPrincipalDimensions.output_log_pos hm).le
  have heq : 2*(rateUpper k c d m*((fixedLength m : ℝ)*Real.log 2))/Real.log (outputSize m : ℝ)=
      overheadCharge k c d m := by
    unfold overheadCharge outputRate
    have hLen : (fixedLength m : ℝ) ≠ 0 := by
      have hh : 0 < fixedLength m := by unfold fixedLength; positivity
      exact_mod_cast hh.ne'
    field_simp [WeightedGlobalPrincipalDimensions.output_log_pos hm |>.ne',hLen,log_two_pos.ne'] <;> ring
  rw [heq] at he
  exact hb.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn.le) he) hBr.le)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeOverhead
