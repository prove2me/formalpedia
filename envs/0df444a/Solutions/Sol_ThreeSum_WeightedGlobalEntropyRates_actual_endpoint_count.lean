-- Prove2me | solution 1 for ThreeSum.WeightedGlobalEntropyRates.actual_endpoint_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:14:56.029765+00:00
-- url     : https://prove2.me/submissions/74d8f4f6-6f88-44ce-8bc1-b7628b746ba6

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_fixedAlpha_total
import Theorems.Thm_ThreeSum_TernaryTypeCardinality_vertices_card_eq_choose


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters WeightedGlobalCoverScale
set_option maxRecDepth 10000
namespace ThreeSum.WeightedGlobalEntropyRates
theorem _root_.solution (m : ℕ) :
    endpointSize m=typeCount 30000000000000 2672750671000 292746547000 m := by
  unfold endpointSize
  rw [TernaryTypeCardinality.vertices_card_eq_choose (fixedAlpha m) (fixedAlpha_total m)]
  change (30000000000000*m).choose (292746547000*m)*(30000000000000*m-292746547000*m).choose (2672750671000*m)=
    (30000000000000*m).choose (292746547000*m)*((30000000000000-292746547000)*m).choose (2672750671000*m)
  rw [← Nat.sub_mul]
end ThreeSum.WeightedGlobalEntropyRates
