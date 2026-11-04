-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaQueryModel.position_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:35:08.29044+00:00
-- url     : https://prove2.me/submissions/9e18ae5f-39fc-449a-aeee-423b0ce38ff6

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryAddressDecode
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchProvenance
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Theorems.Thm_Light_Seg_get
import Theorems.Thm_ThreeSum_TernaryWantedBatchProvenance_emit_decode


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
    (positions : ℕ → ℕ) (n : ℕ) (j : Fin (queries (r := r) maps τ targets positions n).length) :
    (get (queries (r := r) maps τ targets positions n) j.val).1 =
      positions (descriptor maps τ targets positions n j).1 := by
  exact (congrArg (fun e : Entry => e.1) (emit_decode p (4^fixedLength m) F r
    (WeightedGlobalGoodOutputCatalog.raws maps τ) (WeightedGlobalGoodOutputCatalog.wordCodes maps τ)
    (WeightedGlobalGoodOutputCatalog.mapCodes maps τ) targets positions n j)).symm
end ThreeSum.WeightedGlobalArenaQueryModel
