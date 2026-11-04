-- Prove2me | solution 1 for ThreeSum.TernaryParameters.queryEntropy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:55:05.143946+00:00
-- url     : https://prove2.me/submissions/97410973-c54c-4e07-ac7f-e0d47f665c97

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Theorems.Thm_ThreeSum_TernaryParameters_log_two_pos
import Theorems.Thm_ThreeSum_TernaryParameters_log_z_bounds
import Theorems.Thm_ThreeSum_Parameters_log_two_pos

noncomputable section
namespace ThreeSum.TernaryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
private theorem log_two_bounds :
    (13862943611198906187 / 20000000000000000000 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (17328679513998632737 / 25000000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((1 / 3 : ℝ) : ℝ)| < 1) 20
  have hratio : ((1 + (1 / 3 : ℝ)) / (1 - (1 / 3 : ℝ)) : ℝ) = 2 := by
    norm_num []
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]
private theorem log_queryArg1_bounds :
    (58034941144716541 / 800000000000000000 : ℝ) ≤ Real.log queryArg1 ∧ Real.log queryArg1 ≤ (3627183821544783813 / 50000000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((752397677 / 20752397677 : ℝ) : ℝ)| < 1) 20
  have hratio : ((1 + (752397677 / 20752397677 : ℝ)) / (1 - (752397677 / 20752397677 : ℝ)) : ℝ) = queryArg1 := by
    norm_num [queryArg1]
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]
private theorem log_queryArg2_bounds :
    (7779475863001095251 / 100000000000000000000 : ℝ) ≤ Real.log queryArg2 ∧ Real.log queryArg2 ≤ (1944868965750273813 / 25000000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((8090079034354996329 / 208090079034354996329 : ℝ) : ℝ)| < 1) 20
  have hratio : ((1 + (8090079034354996329 / 208090079034354996329 : ℝ)) / (1 - (8090079034354996329 / 208090079034354996329 : ℝ)) : ℝ) = queryArg2 := by
    norm_num [queryArg2]
  rw [hratio] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1, hh.2]
end ThreeSum.TernaryParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
namespace ThreeSum.TernaryParameters
theorem _root_.solution : (700882094933297871 / 10000000000000000000 : ℝ) ≤ queryEntropy ∧ queryEntropy ≤ (43805130933331117 / 625000000000000000 : ℝ) := by
  have h_queryArg1 := log_queryArg1_bounds
  have h_queryArg2 := log_queryArg2_bounds
  have h_z := log_z_bounds
  have h_two := log_two_bounds
  constructor
  · unfold queryEntropy
    apply (le_div_iff₀ log_two_pos).2
    norm_num [queryEntropy, mean, deficit, pi0, pi1, pi2, alpha0, alpha1, alpha2] at *
    linarith [h_queryArg1.1, h_queryArg1.2, h_queryArg2.1, h_queryArg2.2, h_z.1, h_z.2, h_two.1, h_two.2]
  · unfold queryEntropy
    apply (div_le_iff₀ log_two_pos).2
    norm_num [queryEntropy, mean, deficit, pi0, pi1, pi2, alpha0, alpha1, alpha2] at *
    linarith [h_queryArg1.1, h_queryArg1.2, h_queryArg2.1, h_queryArg2.2, h_z.1, h_z.2, h_two.1, h_two.2]
end ThreeSum.TernaryParameters
