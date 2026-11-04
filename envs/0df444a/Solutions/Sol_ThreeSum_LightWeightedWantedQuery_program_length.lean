-- Prove2me | solution 1 for ThreeSum.LightWeightedWantedQuery.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:24:30.786685+00:00
-- url     : https://prove2.me/submissions/344bb48b-4fe6-492b-a188-3f765f9576c0

import Definitions.Def_Submission_Weighted_NearPair
import Definitions.Def_Submission_Weighted_FrozenPhysical
import Definitions.Def_Submission_Weighted_BankAssembly
import Definitions.Def_Submission_Weighted_WantedQuery

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedWantedQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.WeightedBankStageModel
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.LightWeightedNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedWantedQuery
theorem _root_.solution : program.length=40 := rfl
end ThreeSum.LightWeightedWantedQuery
