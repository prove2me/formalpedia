-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates.prime_rate_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:27:57.156193+00:00
-- url     : https://prove2.me/submissions/35e765b8-414a-4536-a12f-131c18c1f884

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryEntropyRates
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalEntropyRates_partition_log
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalEntropyRates_denominator_pos
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverScale_outputSize_ge_sixteen
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverScale_prime_lower
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverScale_prime_upper
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_log_two_pos


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters WeightedGlobalCoverScale
set_option maxRecDepth 10000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates
theorem _root_.solution {m : ℕ} (hm : 0 < m) :
    (outputRate m+WeightedGlobalParameters.partitionEntropy)/2 ≤ primeRate m ∧
    primeRate m ≤ (outputRate m+WeightedGlobalParameters.partitionEntropy)/2+
      Real.log 16/(2*((fixedLength m : ℝ)*Real.log 2)) := by
  have hM : 0 < (outputSize m : ℝ) := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < (16 : ℕ)) (outputSize_ge_sixteen hm)
  have hR : 0 < (partitionCap m : ℝ) := by unfold partitionCap; positivity
  have hp : 0 < (prime m : ℝ) := by exact_mod_cast (prime_prime m).pos
  have hlo : (outputSize m : ℝ)*(partitionCap m : ℝ) ≤ (prime m : ℝ)^2 := by
    exact_mod_cast prime_lower m
  have hup : (prime m : ℝ)^2 ≤ 16*((outputSize m : ℝ)*(partitionCap m : ℝ)) := by
    exact_mod_cast prime_upper m
  have hl := Real.log_le_log (mul_pos hM hR) hlo
  have hu := Real.log_le_log (pow_pos hp 2) hup
  rw [Real.log_mul hM.ne' hR.ne',Real.log_pow,partition_log] at hl
  rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (mul_pos hM hR).ne',
    Real.log_mul hM.ne' hR.ne',Real.log_pow,partition_log] at hu
  norm_num at hl hu
  have hd := denominator_pos hm
  have hL : (fixedLength m : ℝ) ≠ 0 := by
    have hLp : 0 < fixedLength m := by unfold fixedLength; positivity
    exact_mod_cast hLp.ne'
  unfold outputRate primeRate
  constructor
  · apply (le_div_iff₀ hd).mpr
    field_simp [hL,WeightedGlobalParameters.log_two_pos.ne']
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    field_simp [hL,WeightedGlobalParameters.log_two_pos.ne']
    nlinarith
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates
