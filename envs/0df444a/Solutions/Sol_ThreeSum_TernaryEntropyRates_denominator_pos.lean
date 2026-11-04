-- Prove2me | solution 1 for ThreeSum.TernaryEntropyRates.denominator_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:42:15.88197+00:00
-- url     : https://prove2.me/submissions/8399dc8c-8d62-4d3b-85fe-eca341fb4e86

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
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
    0 < (fixedLength m : ℝ)*Real.log 2 := by
  have hL : 0 < fixedLength m := by unfold fixedLength; positivity
  exact mul_pos (by exact_mod_cast hL) TernaryParameters.log_two_pos
end ThreeSum.TernaryEntropyRates
