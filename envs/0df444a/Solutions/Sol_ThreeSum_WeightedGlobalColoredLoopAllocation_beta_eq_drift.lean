-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredLoopAllocation.beta_eq_drift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:46:17.951996+00:00
-- url     : https://prove2.me/submissions/a3079faa-663d-4c9d-994e-640e0826fbfa

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocation

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopAllocation
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalArenaPrefixFootprints
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}
namespace ThreeSum.WeightedGlobalColoredLoopAllocation
theorem _root_.solution (P : Profile κ) :
    9*WeightedGlobalArenaBudgetExistence.pairFactor P.m P.F P.K=P.drift := by
  unfold WeightedGlobalArenaBudgetExistence.pairFactor Profile.drift Profile.M
    WeightedGlobalCoverScale.outputSize WeightedGlobalGoodOutputCatalog.Rbar
  ring
end ThreeSum.WeightedGlobalColoredLoopAllocation
