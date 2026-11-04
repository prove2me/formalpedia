-- Prove2me | solution 1 for ThreeSum.LightTernaryWantedQuery.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:22:00.640902+00:00
-- url     : https://prove2.me/submissions/53995128-eefc-4fe5-bca6-d848ffb310c6

import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPhysical
import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedQuery

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryWantedQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryBankStageModel
open ThreeSum.LightTernaryNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryWantedQuery
theorem _root_.solution : program.length=22 := rfl
end ThreeSum.LightTernaryWantedQuery
