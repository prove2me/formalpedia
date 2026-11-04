-- Prove2me | solution 1 for ThreeSum.LightWeightedBankStages.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:52:58.0622+00:00
-- url     : https://prove2.me/submissions/6721cbe2-9731-4e86-9a8c-4d5bf4e87d69

import Definitions.Def_Submission_Weighted_BankSweep
import Definitions.Def_Submission_Weighted_BankStages

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankStages
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedBankStages
theorem _root_.solution (inverse : Bool) : (program inverse).length=10 := by rfl
end ThreeSum.LightWeightedBankStages
