-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.pi_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:08:34.91224+00:00
-- url     : https://prove2.me/submissions/001f7ee0-25fa-407a-8e38-fed81ae66392

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution : 0 < pi0 ∧ 0 < pi1 ∧ 0 < pi2 := by norm_num [pi0, pi1, pi2]
end ThreeSum.WeightedGlobalParameters
