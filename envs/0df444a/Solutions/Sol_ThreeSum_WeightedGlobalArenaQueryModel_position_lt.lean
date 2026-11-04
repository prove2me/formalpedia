-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaQueryModel.position_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:44:48.576092+00:00
-- url     : https://prove2.me/submissions/6b793399-413e-4339-8a57-581350ba1b32

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryAddressDecode
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchProvenance
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_position_code
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
theorem _root_.solution (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ)
    (positions : ℕ → ℕ) (n originalCount : ℕ) (hpos : ∀ t < n, positions t < originalCount)
    (j : Fin (queries (r := r) maps τ targets positions n).length) :
    (get (queries (r := r) maps τ targets positions n) j.val).1 < originalCount := by
  rw [position_code]
  exact hpos _ (descriptor_spec maps τ targets positions n j).1
end ThreeSum.WeightedGlobalArenaQueryModel
