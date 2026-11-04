-- Prove2me | solution 1 for ThreeSum.WeightedGlobalSignedFeatureHash.left_hash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:56:40.178996+00:00
-- url     : https://prove2.me/submissions/5b2694d0-f8d4-45a4-9864-8ee7b85b584b

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_Submission_Weighted_Global_TernaryNativeRequesterCoverage
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Definitions.Def_Submission_Weighted_Global_TernarySignedFeatureHash
import Theorems.Thm_ThreeSum_WeightedGlobalSignedFeatureHash_hash_raw

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalSignedFeatureHash
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
variable {p J r : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalSignedFeatureHash
theorem _root_.solution (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p)) (U radix : ℕ) (b : ℤ) :
    hash H (fun i => (feature (leftRaw U radix J b) i.val : ZMod p))=sourceLeft H U radix b :=
  hash_raw H _
end ThreeSum.WeightedGlobalSignedFeatureHash
