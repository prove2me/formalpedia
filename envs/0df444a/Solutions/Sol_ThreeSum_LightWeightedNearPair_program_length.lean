-- Prove2me | solution 1 for ThreeSum.LightWeightedNearPair.program_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:08:02.525631+00:00
-- url     : https://prove2.me/submissions/8e94c944-f2e8-443e-bb97-7b65ba5b6ec5

import Definitions.Def_Submission_Weighted_KernelProgram
import Definitions.Def_Submission_Weighted_NearSourceWords
import Definitions.Def_Submission_Weighted_NearPair

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedNearPair
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
namespace ThreeSum.LightWeightedNearPair
theorem _root_.solution : program.length=39 := rfl
end ThreeSum.LightWeightedNearPair
