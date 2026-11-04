-- Prove2me | solution 1 for ThreeSum.LightTernaryPreparedWanted.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:42:33.052686+00:00
-- url     : https://prove2.me/submissions/406813fc-5806-4fc6-8c64-ed7a81de85ef

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryPlan
import Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
import Definitions.Def_Submission_ThreeSum_LightTernaryPreparedWanted

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPreparedWanted
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryBankStageModel ThreeSum.LightTernaryNearPair ThreeSum.LightTernaryQueryPlan
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryPreparedWanted
theorem _root_.solution : program.length=28 := rfl
end ThreeSum.LightTernaryPreparedWanted
