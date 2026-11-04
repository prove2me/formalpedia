-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.alpha_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:05:03.890814+00:00
-- url     : https://prove2.me/submissions/88f8c1f0-9626-420a-adc7-93a4b9f6c090

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution : 0 < alpha0 ∧ 0 < alpha1 ∧ 0 < alpha2 := by
  norm_num [alpha0, alpha1, alpha2]
end ThreeSum.WeightedGlobalParameters
