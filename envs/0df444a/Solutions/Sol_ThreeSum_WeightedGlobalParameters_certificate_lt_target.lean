-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.certificate_lt_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:06:00.701272+00:00
-- url     : https://prove2.me/submissions/24723354-f3e1-4d05-b4c8-1eca4414c7d3

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution : certificateExponent < targetExponent := by
  norm_num [targetExponent, certificateExponent]
end ThreeSum.WeightedGlobalParameters
