-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.weighted_endpoint_below_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:40:34.869488+00:00
-- url     : https://prove2.me/submissions/ca176aef-bd47-4ddb-9671-ed1d4076dfaf

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution : 1025*(alpha1+2*alpha2)<2*cutSlope := by
  norm_num [alpha1,alpha2,cutSlope]
end ThreeSum.WeightedGlobalParameters
