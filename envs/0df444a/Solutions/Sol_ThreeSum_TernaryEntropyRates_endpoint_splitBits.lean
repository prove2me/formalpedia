-- Prove2me | solution 1 for ThreeSum.TernaryEntropyRates.endpoint_splitBits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:59:40.783907+00:00
-- url     : https://prove2.me/submissions/62b18fef-8ee7-4f44-8278-369a43f483bb

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
import Theorems.Thm_ThreeSum_TernaryEntropyRates_entropy_split
import Theorems.Thm_ThreeSum_TernaryJointType_CertifiedParameters_alpha_positive
import Theorems.Thm_ThreeSum_TernaryParameters_alpha_positive
import Theorems.Thm_ThreeSum_TernaryParameters_alpha_total


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal TernaryLocalParameters TernaryCoverScale
set_option maxRecDepth 10000
namespace ThreeSum.TernaryEntropyRates
theorem _root_.solution : splitBits 100000000 8908493 978268 = TernaryParameters.Halpha := by
  have h := entropy_split TernaryParameters.alpha_positive.1 TernaryParameters.alpha_positive.2.1
    TernaryParameters.alpha_positive.2.2 TernaryParameters.alpha_total
  unfold splitBits ThreeSum.Parameters.entropy TernaryParameters.Halpha
  norm_num [TernaryParameters.alpha0,TernaryParameters.alpha1,TernaryParameters.alpha2] at h ⊢
  linear_combination h / Real.log 2
end ThreeSum.TernaryEntropyRates
