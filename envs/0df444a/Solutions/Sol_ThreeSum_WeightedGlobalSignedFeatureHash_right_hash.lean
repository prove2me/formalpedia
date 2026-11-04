-- Prove2me | solution 1 for ThreeSum.WeightedGlobalSignedFeatureHash.right_hash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:03:04.864332+00:00
-- url     : https://prove2.me/submissions/056412f6-e225-4a92-a39a-f8436beb7c94

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
theorem _root_.solution (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p)) (U radix : ℕ) (c : ℤ) :
    hash H (fun i => (feature (rightRaw U radix J c) i.val : ZMod p))=sourceRight H U radix c :=
  hash_raw H _
end ThreeSum.WeightedGlobalSignedFeatureHash
