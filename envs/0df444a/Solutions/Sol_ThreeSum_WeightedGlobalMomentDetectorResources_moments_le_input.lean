-- Prove2me | solution 1 for ThreeSum.WeightedGlobalMomentDetectorResources.moments_le_input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:14:52.554481+00:00
-- url     : https://prove2.me/submissions/35c37842-af5a-48d6-a582-777da103738d

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDetectorResources
import Theorems.Thm_ThreeSum_WeightedGlobalMomentDetectorResources_detectorInput_le
import Theorems.Thm_ThreeSum_WeightedGlobalNativeMomentBounds_detector_moments_bound


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentDetectorResources
open WeightedGlobalNativeMomentBounds StageBounds
namespace ThreeSum.WeightedGlobalMomentDetectorResources
theorem _root_.solution {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (B U H : ℕ) (hpairs : pairBound S*2^N≤B) (left right : ℕ→ℤ)
    (hleft : ∀ j<S.left.NL, |left j|≤(U : ℤ))
    (hright : ∀ j<S.right.NL, |right j|≤(U : ℤ)) :
    ∀ i, ∀ k≤2*H,
      |∑ p : WeightedGlobalNativePairMoments.Pair S i,
        WeightedGlobalNativePairMoments.mass S i p*WeightedGlobalNativePairMoments.mode left right p^k|
        ≤(input B U H : ℤ) := by
  intro i k hk
  exact (detector_moments_bound S left right hleft hright i k hk).trans
    (by exact_mod_cast detectorInput_le S B U H hpairs)
end ThreeSum.WeightedGlobalMomentDetectorResources
