-- Prove2me | solution 1 for ThreeSum.WeightedGlobalSignedFeatureHash.hash_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:44:33.478868+00:00
-- url     : https://prove2.me/submissions/f28a064f-1551-4bc5-abdf-1441a2840dfb

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_Submission_Weighted_Global_TernaryNativeRequesterCoverage
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
import Theorems.Thm_ThreeSum_WeightedGlobalSignedFeatureHash_unfeature_cast

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalSignedFeatureHash
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
variable {p J r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalSignedFeatureHash
theorem _root_.solution (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (raw : Coordinate J→ℤ) :
    hash H (fun i => (feature raw i.val : ZMod p))=H (field raw) := by
  exact congrArg H (unfeature_cast raw)
end ThreeSum.WeightedGlobalSignedFeatureHash
