-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeRates.inflation_rate_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:13:56.708709+00:00
-- url     : https://prove2.me/submissions/26413670-eb48-4d66-b27d-97764ca210d3

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryOversizeRates
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalEntropyRates_denominator_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizePrime_inflation_lower
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizePrime_inflation_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizePrime_inflation_upper
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalOversizePrime_outputSize_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_log_two_pos


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeRates
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters WeightedGlobalOversizePrime
open scoped Topology
set_option maxHeartbeats 1000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeRates
theorem _root_.solution {K m : ℕ} (hK : 0 < K) (hm : 0 < m) :
    outputRate m/K ≤ inflationRate K m ∧
      inflationRate K m ≤ outputRate m/K+Real.log 2/((fixedLength m : ℝ)*Real.log 2) := by
  have hMr : 0 < (outputSize m : ℝ) := by exact_mod_cast outputSize_pos m
  have hSr : 0 < (inflation K m : ℝ) := by exact_mod_cast inflation_pos hK m
  have hl : (outputSize m : ℝ) ≤ (inflation K m : ℝ)^K := by exact_mod_cast inflation_lower hK m
  have hu : (inflation K m : ℝ)^K ≤ (2 : ℝ)^K*(outputSize m : ℝ) := by exact_mod_cast inflation_upper hK m
  have hlo := Real.log_le_log hMr hl
  have hup := Real.log_le_log (pow_pos hSr _) hu
  rw [Real.log_pow] at hlo
  rw [Real.log_pow,Real.log_mul (pow_pos (by norm_num : (0 : ℝ) < 2) _).ne' hMr.ne',Real.log_pow] at hup
  have hkR : (0 : ℝ) < K := by exact_mod_cast hK
  have hd := denominator_pos hm
  have hL : (fixedLength m : ℝ) ≠ 0 := by
    have hLp : 0 < fixedLength m := by unfold fixedLength; positivity
    exact_mod_cast hLp.ne'
  unfold outputRate inflationRate
  constructor
  · apply (le_div_iff₀ hd).mpr
    field_simp [hL,log_two_pos.ne',hkR.ne']
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    field_simp [hL,log_two_pos.ne',hkR.ne']
    nlinarith
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalOversizeRates
