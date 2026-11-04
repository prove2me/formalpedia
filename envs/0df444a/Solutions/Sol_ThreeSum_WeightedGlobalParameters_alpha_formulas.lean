-- Prove2me | solution 1 for ThreeSum.WeightedGlobalParameters.alpha_formulas
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:40:10.7972+00:00
-- url     : https://prove2.me/submissions/d6ea64e9-f65c-4396-9c30-19a3113a2677

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeSum.WeightedGlobalParameters
theorem _root_.solution :
    alpha0 = pi0 + pi1 / 2 + pi2 / 3 ∧
    alpha1 = pi1 / 2 + pi2 / 3 ∧ alpha2 = pi2 / 3 := by
  norm_num [alpha0, alpha1, alpha2, pi0, pi1, pi2]
end ThreeSum.WeightedGlobalParameters
