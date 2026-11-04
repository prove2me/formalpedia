-- Prove2me | solution 1 for ThreeSum.LightWeightedCost.partialCost_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:30:22.779867+00:00
-- url     : https://prove2.me/submissions/895b84fe-5d8f-4996-9e0c-762a67b15a43

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_Weighted_LightCost

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedCost
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
open ThreeSum.WeightedEnumeration
open Light Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.LightSubsetAddress
namespace ThreeSum.LightWeightedCost
theorem _root_.solution (N m j : ℕ) :
    partialCost N m (j+1)=partialCost N m j+digitCost (digitAt N m j) := sum_range_succ _ _
end ThreeSum.LightWeightedCost
