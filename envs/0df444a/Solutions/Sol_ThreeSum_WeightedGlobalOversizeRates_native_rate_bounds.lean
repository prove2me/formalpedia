-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeRates.native_rate_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:56:50.275931+00:00
-- url     : https://prove2.me/submissions/742a616c-9335-44d3-adbf-032b12d4d4ae

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_denominator_pos
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_partition_log
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_inflation_pos
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_nativePrime_lower
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_nativePrime_upper
import Theorems.Thm_ThreeSum_WeightedGlobalOversizePrime_outputSize_pos
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_log_two_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeRates
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalOversizeRates
theorem _root_.solution {K m : ℕ} (hK : 0 < K) (hm : 0 < m) :
    (outputRate m+partitionEntropy)/2+inflationRate K m ≤ nativeRate K m ∧
    nativeRate K m ≤ (outputRate m+partitionEntropy)/2+inflationRate K m+
      Real.log 16/(2*((fixedLength m : ℝ)*Real.log 2)) := by
  have hM : 0 < (outputSize m : ℝ) := by exact_mod_cast outputSize_pos m
  have hR : 0 < (partitionCap m : ℝ) := by unfold partitionCap; positivity
  have hS : 0 < (inflation K m : ℝ) := by exact_mod_cast inflation_pos hK m
  have hp : 0 < (nativePrime K m : ℝ) := by exact_mod_cast (nativePrime_prime K m).pos
  have hlo : ((outputSize m : ℝ)*(partitionCap m : ℝ))*(inflation K m : ℝ)^2 ≤ (nativePrime K m : ℝ)^2 := by
    exact_mod_cast nativePrime_lower K m
  have hup : (nativePrime K m : ℝ)^2 ≤ 16*(((outputSize m : ℝ)*(partitionCap m : ℝ))*(inflation K m : ℝ)^2) := by
    exact_mod_cast nativePrime_upper hK m
  have hl := Real.log_le_log (mul_pos (mul_pos hM hR) (pow_pos hS _)) hlo
  have hu := Real.log_le_log (pow_pos hp 2) hup
  rw [Real.log_mul (mul_pos hM hR).ne' (pow_pos hS _).ne',Real.log_mul hM.ne' hR.ne',
    Real.log_pow,Real.log_pow,partition_log] at hl
  rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (mul_pos (mul_pos hM hR) (pow_pos hS _)).ne',
    Real.log_mul (mul_pos hM hR).ne' (pow_pos hS _).ne',Real.log_mul hM.ne' hR.ne',
    Real.log_pow,Real.log_pow,partition_log] at hu
  norm_num at hl hu
  have hd := denominator_pos hm
  have hL : (fixedLength m : ℝ) ≠ 0 := by
    have hLp : 0 < fixedLength m := by unfold fixedLength; positivity
    exact_mod_cast hLp.ne'
  unfold outputRate nativeRate inflationRate
  constructor
  · apply (le_div_iff₀ hd).mpr
    field_simp [hL,log_two_pos.ne']
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    field_simp [hL,log_two_pos.ne']
    nlinarith
end ThreeSum.WeightedGlobalOversizeRates
