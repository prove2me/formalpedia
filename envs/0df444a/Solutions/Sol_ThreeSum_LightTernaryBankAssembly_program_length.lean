-- Prove2me | solution 1 for ThreeSum.LightTernaryBankAssembly.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:02:06.92491+00:00
-- url     : https://prove2.me/submissions/2c5a8c19-e4ca-49af-8391-842bf93689ba

import Definitions.Def_Submission_ThreeSum_LightTernaryBankStages
import Definitions.Def_Submission_ThreeSum_LightTernaryProduct
import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankAssembly
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 6000000
variable {lim : Limits}
namespace ThreeSum.LightTernaryBankAssembly
theorem _root_.solution : program.length=17 := rfl
end ThreeSum.LightTernaryBankAssembly
