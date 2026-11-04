-- Prove2me | solution 1 for ThreeSum.LightWeightedBankAssembly.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:59:17.199452+00:00
-- url     : https://prove2.me/submissions/7a63e6fd-b93c-4aa8-88d9-2f61b4f46315

import Definitions.Def_Submission_Weighted_BankStages
import Definitions.Def_Submission_ThreeSum_LightTernaryProduct
import Definitions.Def_Submission_Weighted_BankAssembly

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankAssembly
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 6000000
variable {lim : Limits}
namespace ThreeSum.LightWeightedBankAssembly
theorem _root_.solution : program.length=17 := rfl
end ThreeSum.LightWeightedBankAssembly
