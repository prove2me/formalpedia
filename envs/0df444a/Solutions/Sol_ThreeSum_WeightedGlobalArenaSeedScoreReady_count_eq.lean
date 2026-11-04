-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaSeedScoreReady.count_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:29:09.631544+00:00
-- url     : https://prove2.me/submissions/d3c7e697-a4b9-4f7a-9fd6-4aaabd4f42a9

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedCandidate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorReady
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedScoreReady
import Theorems.Thm_ThreeSum_TernaryWantedBatchIndex_entries_length_eq_count
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceCountSeed_seed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceSeed_seed


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSeedScoreReady
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend WeightedGlobalArenaLayout
open LightWeightedGlobalSeedScoreFactory WeightedGlobalArenaSeedCandidate
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
namespace ThreeSum.WeightedGlobalArenaSeedScoreReady
theorem _root_.solution (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (seed : ℕ)
    (D : Data (config p r I A seed)) :
    (setup (r := r) maps τ cap Q (sourceInput I A seed D)).front.count=
      D.H (4^fixedLength m) F (WeightedGlobalGoodOutputCatalog.raws maps τ)
        (WeightedGlobalGoodOutputCatalog.wordCodes maps τ) (WeightedGlobalGoodOutputCatalog.mapCodes maps τ) := by
  exact TernaryWantedBatchIndex.entries_length_eq_count _ _ _ _ _ _ _ _ _ _
end ThreeSum.WeightedGlobalArenaSeedScoreReady
