-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaControllerCore.runtime_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:45:32.204578+00:00
-- url     : https://prove2.me/submissions/48a3bf26-5e5d-4ea8-b7d9-dbe6c8d75772

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
theorem _root_.solution {C : Config} [Fact C.p.Prime] (D : Family C)
    (K R S n : ℕ) (raws : List ℤ) (words maps : List ℕ) (i : ℕ) (hi : i < n) :
    (D.candidate i).runtime K R S raws words maps ≤ seedTime D K R S n raws words maps :=
  by
    exact Finset.le_sup (f := fun i => (D.candidate i).runtime K R S raws words maps) (Finset.mem_range.mpr hi)
end ThreeSum.WeightedGlobalArenaControllerCore
