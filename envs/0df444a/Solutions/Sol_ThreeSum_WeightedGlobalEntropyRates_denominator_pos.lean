-- Prove2me | solution 1 for ThreeSum.WeightedGlobalEntropyRates.denominator_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:40:54.121527+00:00
-- url     : https://prove2.me/submissions/dce52983-3e88-4a8a-b901-bc60113ef74b

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_log_two_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters WeightedGlobalCoverScale
set_option maxRecDepth 10000
namespace ThreeSum.WeightedGlobalEntropyRates
theorem _root_.solution {m : ℕ} (hm : 0 < m) :
    0 < (fixedLength m : ℝ)*Real.log 2 := by
  have hL : 0 < fixedLength m := by unfold fixedLength; positivity
  exact mul_pos (by exact_mod_cast hL) WeightedGlobalParameters.log_two_pos
end ThreeSum.WeightedGlobalEntropyRates
