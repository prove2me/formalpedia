-- Prove2me | solution 1 for ThreeSum.WeightedGlobalMomentDetectorResources.detectorInput_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:25:41.609205+00:00
-- url     : https://prove2.me/submissions/072a8f4b-2360-4400-8969-7a4cc21db03b

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDetectorResources

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentDetectorResources
open WeightedGlobalNativeMomentBounds StageBounds
namespace ThreeSum.WeightedGlobalMomentDetectorResources
theorem _root_.solution {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (B U H : ℕ) (hpairs : pairBound S*2^N≤B) :
    detectorInput S U H ≤ input B U H := by
  unfold detectorInput momentBound input
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hpairs) _
end ThreeSum.WeightedGlobalMomentDetectorResources
