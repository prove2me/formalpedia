-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentDetectorResources.moments_le_input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:57:54.133004+00:00
-- url     : https://prove2.me/submissions/ed6808ad-0530-4700-9174-7fb953250f66

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentDetectorResources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalMomentDetectorResources_detectorInput_le
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeMomentBounds_detector_moments_bound


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentDetectorResources
open WeightedGlobalNativeMomentBounds StageBounds
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentDetectorResources
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentDetectorResources
