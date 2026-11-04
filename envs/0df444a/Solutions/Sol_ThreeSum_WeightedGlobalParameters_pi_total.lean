-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.pi_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:05:00.383982+00:00
-- url     : https://prove2.me/submissions/669d66a4-544d-4a2d-94e1-5043c850f492

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution : pi0 + pi1 + pi2 = 1 := by norm_num [pi0, pi1, pi2]
end ThreeSum.WeightedGlobalParameters
