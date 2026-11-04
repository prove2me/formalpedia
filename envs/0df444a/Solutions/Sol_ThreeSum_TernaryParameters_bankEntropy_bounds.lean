-- Prove2me | solution 1 for ThreeSum.TernaryParameters.bankEntropy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:55:51.888016+00:00
-- url     : https://prove2.me/submissions/a3c26daf-3325-41ad-b093-6719eefb0c4b

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Theorems.Thm_ThreeSum_TernaryParameters_log_two_pos
import Theorems.Thm_ThreeSum_TernaryParameters_log_y_bounds
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
private theorem log_bankArg_bounds :
    (1215161922777427739 / 6250000000000000000 : ℝ) ≤ Real.log bankArg ∧ Real.log bankArg ≤ (777703630577553753 / 4000000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le
    (by norm_num : |((21461348597670952401 / 221461348597670952401 : ℝ) : ℝ)| < 1) 20
  have hratio : ((1 + (21461348597670952401 / 221461348597670952401 : ℝ)) / (1 - (21461348597670952401 / 221461348597670952401 : ℝ)) : ℝ) = bankArg := by
    norm_num [bankArg]
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
theorem _root_.solution : (24442778518278711 / 31250000000000000 : ℝ) ≤ bankEntropy ∧ bankEntropy ≤ (1955422281462296881 / 2500000000000000000 : ℝ) := by
  have h_bankArg := log_bankArg_bounds
  have h_y := log_y_bounds
  have h_two := log_two_bounds
  constructor
  · unfold bankEntropy
    apply (le_div_iff₀ log_two_pos).2
    norm_num [bankEntropy, mean, deficit, pi0, pi1, pi2, alpha0, alpha1, alpha2] at *
    linarith [h_bankArg.1, h_bankArg.2, h_y.1, h_y.2, h_two.1, h_two.2]
  · unfold bankEntropy
    apply (div_le_iff₀ log_two_pos).2
    norm_num [bankEntropy, mean, deficit, pi0, pi1, pi2, alpha0, alpha1, alpha2] at *
    linarith [h_bankArg.1, h_bankArg.2, h_y.1, h_y.2, h_two.1, h_two.2]
end ThreeSum.TernaryParameters
