-- Prove2me | solution 1 for ThreeSum.LightTernaryBankStages.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:56:13.69484+00:00
-- url     : https://prove2.me/submissions/8b201956-3622-4c0a-a773-03ef0bcc1546

import Definitions.Def_Submission_ThreeSum_LightTernaryBankSweep
import Definitions.Def_Submission_ThreeSum_LightTernaryBankStages

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankStages
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryBankStages
theorem _root_.solution (inverse : Bool) : (program inverse).length=10 := by rfl
end ThreeSum.LightTernaryBankStages
