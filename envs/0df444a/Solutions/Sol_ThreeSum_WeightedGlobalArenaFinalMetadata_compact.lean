-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaFinalMetadata.compact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T23:09:03.228733+00:00
-- url     : https://prove2.me/submissions/fcc0f0b0-bcc0-488a-b97f-02f135f96096

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedScoreReady
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPostMemory
import Definitions.Def_Submission_Weighted_Global_LightTernaryControllerFull
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFinalMetadata

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaFinalMetadata
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory WeightedGlobalArenaPostMemory
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaFinalMetadata
theorem _root_.solution {maps : Fin F→Weight m p} {τ : ℕ} {I : Input} {μ : ℕ→ℤ}
    (M : Metadata (r := r) maps τ I μ) (nB nC : ℕ) (fB fC : ℕ→ℕ) :
    Metadata (r := r) maps τ (WeightedGlobalArenaPairRestriction.restrict I nB nC fB fC) μ := by
  exact ⟨M.codes,M.powers,M.wanted⟩
end ThreeSum.WeightedGlobalArenaFinalMetadata
