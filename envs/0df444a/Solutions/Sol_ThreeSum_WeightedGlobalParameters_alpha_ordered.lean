-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.alpha_ordered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:38:23.877639+00:00
-- url     : https://prove2.me/submissions/b115518c-0e95-4267-9140-bb8dc00745fd

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution : alpha2 ≤ alpha1 ∧ alpha1 ≤ alpha0 := by
  norm_num [alpha0, alpha1, alpha2]
end ThreeSum.WeightedGlobalParameters
