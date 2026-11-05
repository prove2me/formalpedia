-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopAllocation.beta_eq_drift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:16:43.366991+00:00
-- url     : https://prove2.me/submissions/65ebbea8-1c0c-4fc5-b9e6-530b8fb5dd93

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopAllocation

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopAllocation
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalArenaPrefixFootprints
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopAllocation
theorem _root_.solution (P : Profile κ) :
    9*WeightedGlobalArenaBudgetExistence.pairFactor P.m P.F P.K=P.drift := by
  unfold WeightedGlobalArenaBudgetExistence.pairFactor Profile.drift Profile.M
    WeightedGlobalCoverScale.outputSize WeightedGlobalGoodOutputCatalog.Rbar
  ring
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopAllocation
