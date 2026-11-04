-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaQueryModel.setup_same_type
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:37:58.752199+00:00
-- url     : https://prove2.me/submissions/15fd70d3-1930-4463-a8eb-5c4c08a8b7e0

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryAddressDecode
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchProvenance
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_setup_typed
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_setup_star_typed

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
    ∀ d, digitCount ((WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.Q i) d =
      digitCount ((WeightedGlobalArenaSourceSetup.setup (r := r) maps τ cap localQ I).front.Qstar) d := by
  intro d
  rw [setup_typed hi d,setup_star_typed maps τ cap localQ I d]
end ThreeSum.WeightedGlobalArenaQueryModel
