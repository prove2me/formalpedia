-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.alpha_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:05:05.116101+00:00
-- url     : https://prove2.me/submissions/8c9bfd71-3ac4-42f4-8d6a-336a822ecd76

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution : alpha0 + alpha1 + alpha2 = 1 := by
  norm_num [alpha0, alpha1, alpha2]
end ThreeSum.WeightedGlobalParameters
