-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaControllerCore.flag_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:54:47.662459+00:00
-- url     : https://prove2.me/submissions/372a5e87-1876-4ee5-a895-24dcb45480c5

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaGuardTransport
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerPlan
import Definitions.Def_Submission_Weighted_Global_TernaryArenaControllerCore

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaControllerCore
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaScoreScan
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedGlobalArenaControllerCore
theorem _root_.solution {C : Config} [Fact C.p.Prime] (D : Family C) (i : ℕ) : |D.flag i| ≤ 1 := by
  unfold Family.flag Data.flag LightStoredSpan.admissibleFlag
  split_ifs <;> norm_num
end ThreeSum.WeightedGlobalArenaControllerCore
