-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.log_two_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:50.079633+00:00
-- url     : https://prove2.me/submissions/edc8b4ce-ded4-4f00-b631-4abcc90db9eb

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution :
    (693147180559945309/1000000000000000000 : ℝ)≤Real.log 2 ∧
    Real.log 2≤(69314718055994531/100000000000000000 : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (by norm_num : |(1/3 : ℝ)|<1) 20
  have he : (1+(1/3 : ℝ))/(1-(1/3 : ℝ))=2 := by norm_num
  rw [he] at h
  norm_num [Finset.sum_range_succ] at h
  have hh := abs_le.mp h
  constructor <;> linarith [hh.1,hh.2]
end ThreeSum.WeightedGlobalParameters
