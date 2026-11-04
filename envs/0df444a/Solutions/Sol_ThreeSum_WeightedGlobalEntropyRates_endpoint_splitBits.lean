-- Prove2me | solution 1 for ThreeSum.WeightedGlobalEntropyRates.endpoint_splitBits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:10:17.526075+00:00
-- url     : https://prove2.me/submissions/cdc33ce2-02a1-4758-a071-dc18c2b78dc9

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_entropy_split
import Theorems.Thm_ThreeSum_TernaryJointType_CertifiedParameters_alpha_positive
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_alpha_positive
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_alpha_total


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters WeightedGlobalCoverScale
set_option maxRecDepth 10000
namespace ThreeSum.WeightedGlobalEntropyRates
theorem _root_.solution : splitBits 30000000000000 2672750671000 292746547000 = WeightedGlobalParameters.Halpha := by
  have h := entropy_split WeightedGlobalParameters.alpha_positive.1 WeightedGlobalParameters.alpha_positive.2.1
    WeightedGlobalParameters.alpha_positive.2.2 WeightedGlobalParameters.alpha_total
  unfold splitBits ThreeSum.Parameters.entropy WeightedGlobalParameters.Halpha WeightedCacheParameters.An
  norm_num [WeightedCacheParameters.alpha0,WeightedCacheParameters.alpha1,WeightedCacheParameters.alpha2,WeightedGlobalParameters.alpha0,WeightedGlobalParameters.alpha1,WeightedGlobalParameters.alpha2] at h ⊢
  linear_combination h / Real.log 2
end ThreeSum.WeightedGlobalEntropyRates
