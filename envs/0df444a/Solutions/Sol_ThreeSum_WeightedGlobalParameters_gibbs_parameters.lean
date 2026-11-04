-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.gibbs_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:58:20.485803+00:00
-- url     : https://prove2.me/submissions/7b4fcb3c-90ee-4f9a-a763-ec87ccb272ee

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution : 0<y ∧ y<1 ∧ 0<z ∧ z<1 := by
  norm_num [y,z,WeightedCacheParameters.yRoot,WeightedCacheParameters.zRoot]
end ThreeSum.WeightedGlobalParameters
