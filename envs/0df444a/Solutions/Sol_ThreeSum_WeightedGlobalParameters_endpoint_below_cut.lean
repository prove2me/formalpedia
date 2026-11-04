-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.endpoint_below_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:40:13.164076+00:00
-- url     : https://prove2.me/submissions/e5bae457-4b12-4ac2-8925-4cb26d1a74ab

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution : mean/2<mean-deficit := by norm_num [mean,pi1,pi2,deficit]
end ThreeSum.WeightedGlobalParameters
