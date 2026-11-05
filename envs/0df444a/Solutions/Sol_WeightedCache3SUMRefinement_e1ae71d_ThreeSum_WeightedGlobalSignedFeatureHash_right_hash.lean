-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedFeatureHash.right_hash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:58:59.396447+00:00
-- url     : https://prove2.me/submissions/9d8d0950-bf03-4eeb-bdec-bc9fdea2f798

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeRequesterCoverage
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedFeatureHash
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalSignedFeatureHash_hash_raw

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedFeatureHash
open TernarySignedReduction TernarySignedLayout WeightedGlobalNativeRequesterCoverage
variable {p J r : ℕ} [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedFeatureHash
theorem _root_.solution (H : (Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p)) (U radix : ℕ) (c : ℤ) :
    hash H (fun i => (feature (rightRaw U radix J c) i.val : ZMod p))=sourceRight H U radix c :=
  hash_raw H _
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalSignedFeatureHash
