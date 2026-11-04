-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaQueryModel.setup_address
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:17:58.53092+00:00
-- url     : https://prove2.me/submissions/213c0f97-9efe-4c39-b741-335e4fae4f73

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryAddressDecode
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchProvenance
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_word_code
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_setup_Q
import Theorems.Thm_Light_Seg_get


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
    TernaryCodeSemantics.address ((WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.Q i) =
      (get (WeightedGlobalArenaSourceSetup.entries (r := r) maps τ I) i).2.1 := by
  rw [setup_Q hi]
  exact (word_code maps τ I.targets I.positions I.requesterCount ⟨i,hi⟩).symm
end ThreeSum.WeightedGlobalArenaQueryModel
