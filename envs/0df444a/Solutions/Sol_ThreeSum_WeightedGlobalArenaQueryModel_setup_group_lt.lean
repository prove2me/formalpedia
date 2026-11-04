-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaQueryModel.setup_group_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:01:07.494362+00:00
-- url     : https://prove2.me/submissions/5d6f48d4-9b2d-469a-a979-96a3c075ebf1

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryAddressDecode
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchProvenance
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_group_lt

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
    (hF : 1 < F) {i : ℕ}
    (hi : i < (WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.count) :
    (WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.group i < F^r :=
  group_lt maps τ I.targets I.positions I.requesterCount hF ⟨i,hi⟩
end ThreeSum.WeightedGlobalArenaQueryModel
