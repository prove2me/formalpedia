-- Prove2me | solution 1 for WeightedCacheParameters_e1ae71d.log_queryArg2_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:08:33.74555+00:00
-- url     : https://prove2.me/submissions/2bab8350-a936-4d9c-9d5a-574655391f11

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Theorems.Thm_WeightedCacheParameters_e1ae71d_log_queryArg2_lower_bounds
import Theorems.Thm_WeightedCacheParameters_e1ae71d_log_queryArg2_upper_bounds

set_option autoImplicit false
noncomputable section
open WeightedCacheParameters_e1ae71d
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096
namespace WeightedCacheParameters_e1ae71d
theorem _root_.solution :
    (19387293186940463 / 250000000000000000 : ℝ) ≤ Real.log queryArg2 ∧ Real.log queryArg2 ≤ (15509834549552371 / 200000000000000000 : ℝ) := by
  have hp : (540317684481267861 / 500000000000000000 : ℝ) ≤ queryArg2 ∧ queryArg2 ≤ (1080635368962535723 / 1000000000000000000 : ℝ) := by
    constructor <;> norm_num [queryArg2, zRoot]
  have hl := Real.log_le_log (by norm_num : 0 < (540317684481267861 / 500000000000000000 : ℝ)) hp.1
  have hu := Real.log_le_log (lt_of_lt_of_le (by norm_num : 0 < (540317684481267861 / 500000000000000000 : ℝ)) hp.1) hp.2
  exact ⟨(log_queryArg2_lower_bounds).1.trans hl, hu.trans (log_queryArg2_upper_bounds).2⟩
end WeightedCacheParameters_e1ae71d
