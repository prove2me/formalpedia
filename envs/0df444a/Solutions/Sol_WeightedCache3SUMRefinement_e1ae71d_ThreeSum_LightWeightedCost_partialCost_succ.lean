-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCost.partialCost_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:09:21.574259+00:00
-- url     : https://prove2.me/submissions/e3226195-547e-415a-805c-b1634098c911

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightCost

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCost
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
open ThreeSum.WeightedEnumeration
open Light Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.LightSubsetAddress
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCost
theorem _root_.solution (N m j : ℕ) :
    partialCost N m (j+1)=partialCost N m j+digitCost (digitAt N m j) := sum_range_succ _ _
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedCost
