-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.certificate_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:41:00.402279+00:00
-- url     : https://prove2.me/submissions/fcbe9389-b848-46a3-9d78-fe38adccf89e

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution : targetExponent - certificateExponent = (1/125000000 : ℝ) := by
  norm_num [targetExponent, certificateExponent]
end ThreeSum.WeightedGlobalParameters
