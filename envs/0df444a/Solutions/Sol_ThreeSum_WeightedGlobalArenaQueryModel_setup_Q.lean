-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaQueryModel.setup_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:06:51.873873+00:00
-- url     : https://prove2.me/submissions/d40bfdd0-675a-40cc-9fdc-31d5ce1eb0de

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryAddressDecode
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchProvenance
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_decoded_word

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaQueryModel
open TernaryJointType WeightedGlobalLocalParameters TernaryCoverLocal TernaryCoverHashes WeightedGlobalCoverGoodMaps
open TernaryWantedBatchIndex TernaryWantedBatchProvenance WeightedGlobalRepeatedWords
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
variable {m p F r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaQueryModel
theorem _root_.solution {maps : Fin F → Weight m p} {τ cap : ℕ}
    {localQ : WeightedGlobalGoodOutputCatalog.Output m} {I : WeightedGlobalArenaSourceSetup.Input}
    {i : ℕ} (hi : i < (WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.count) :
    (WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.Q i =
      word maps τ I.targets I.positions I.requesterCount ⟨i,hi⟩ :=
  decoded_word maps τ I.targets I.positions I.requesterCount ⟨i,hi⟩
end ThreeSum.WeightedGlobalArenaQueryModel
