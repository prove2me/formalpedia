-- Prove2me | solution 1 for ThreeSum.TernaryEntropyRates.prime_rate_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:13:32.764502+00:00
-- url     : https://prove2.me/submissions/445ecf62-415e-473d-b724-a28fa4f85753

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
import Theorems.Thm_ThreeSum_TernaryEntropyRates_partition_log
import Theorems.Thm_ThreeSum_TernaryEntropyRates_denominator_pos
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_ThreeSum_TernaryCoverScale_outputSize_ge_sixteen
import Theorems.Thm_ThreeSum_TernaryCoverScale_prime_lower
import Theorems.Thm_ThreeSum_TernaryCoverScale_prime_upper
import Theorems.Thm_ThreeSum_TernaryParameters_log_two_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal TernaryLocalParameters TernaryCoverScale
set_option maxRecDepth 10000
namespace ThreeSum.TernaryEntropyRates
theorem _root_.solution {m : ℕ} (hm : 0 < m) :
    (outputRate m+TernaryParameters.partitionEntropy)/2 ≤ primeRate m ∧
    primeRate m ≤ (outputRate m+TernaryParameters.partitionEntropy)/2+
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
    field_simp [hL,TernaryParameters.log_two_pos.ne']
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    field_simp [hL,TernaryParameters.log_two_pos.ne']
    nlinarith
end ThreeSum.TernaryEntropyRates
