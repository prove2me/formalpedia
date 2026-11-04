-- Prove2me | solution 1 for ThreeSum.WeightedGlobalEntropyRates.output_splitBits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:13:53.387114+00:00
-- url     : https://prove2.me/submissions/149f3950-6d35-4fc0-8ed5-45c8a13b44fb

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_entropy_split
import Theorems.Thm_ThreeSum_TernaryJointType_CertifiedParameters_pi_positive
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_pi_positive
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_pi_total


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters WeightedGlobalCoverScale
set_option maxRecDepth 10000
namespace ThreeSum.WeightedGlobalEntropyRates
theorem _root_.solution : splitBits 30000000000000 4760008248000 878239641000 = WeightedGlobalParameters.Hpi := by
  have h := entropy_split WeightedGlobalParameters.pi_positive.1 WeightedGlobalParameters.pi_positive.2.1
    WeightedGlobalParameters.pi_positive.2.2 WeightedGlobalParameters.pi_total
  unfold splitBits ThreeSum.Parameters.entropy WeightedGlobalParameters.Hpi WeightedCacheParameters.Hn
  norm_num [WeightedCacheParameters.pi0,WeightedCacheParameters.pi1,WeightedCacheParameters.pi2,WeightedGlobalParameters.pi0,WeightedGlobalParameters.pi1,WeightedGlobalParameters.pi2] at h ⊢
  linear_combination h / Real.log 2
end ThreeSum.WeightedGlobalEntropyRates
