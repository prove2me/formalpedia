-- Prove2me | solution 1 for ThreeSum.TernaryEntropyRates.output_splitBits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:59.930087+00:00
-- url     : https://prove2.me/submissions/11575506-900b-44d7-9aed-bc2b87269d52

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
import Theorems.Thm_ThreeSum_TernaryEntropyRates_entropy_split
import Theorems.Thm_ThreeSum_TernaryJointType_CertifiedParameters_pi_positive
import Theorems.Thm_ThreeSum_TernaryParameters_pi_positive
import Theorems.Thm_ThreeSum_TernaryParameters_pi_total


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal TernaryLocalParameters TernaryCoverScale
set_option maxRecDepth 10000
namespace ThreeSum.TernaryEntropyRates
theorem _root_.solution : splitBits 100000000 15860450 2934804 = TernaryParameters.Hpi := by
  have h := entropy_split TernaryParameters.pi_positive.1 TernaryParameters.pi_positive.2.1
    TernaryParameters.pi_positive.2.2 TernaryParameters.pi_total
  unfold splitBits ThreeSum.Parameters.entropy TernaryParameters.Hpi
  norm_num [TernaryParameters.pi0,TernaryParameters.pi1,TernaryParameters.pi2] at h ⊢
  linear_combination h / Real.log 2
end ThreeSum.TernaryEntropyRates
