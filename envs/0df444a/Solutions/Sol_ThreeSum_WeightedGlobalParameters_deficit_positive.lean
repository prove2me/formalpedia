-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.deficit_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:40:11.99551+00:00
-- url     : https://prove2.me/submissions/5d85bc59-08e6-4049-9f37-beb2e1e50e72

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution : 0<deficit := by norm_num [deficit]
end ThreeSum.WeightedGlobalParameters
