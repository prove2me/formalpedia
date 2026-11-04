-- Prove2me | solution 1 for ThreeSum.WeightedGlobalMomentDetectorResources.word_guard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:33:08.532807+00:00
-- url     : https://prove2.me/submissions/8a1bd3a7-2303-432c-92f5-b2492c85920c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDetectorResources
import Theorems.Thm_ThreeSum_WeightedGlobalNativeMomentBounds_detector_word_bound


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentDetectorResources
open WeightedGlobalNativeMomentBounds StageBounds
namespace ThreeSum.WeightedGlobalMomentDetectorResources
theorem _root_.solution (B U H : ℕ) (lim : Light.Limits)
    (hw : ((need B U H).word : ℤ)≤lim.word) :
    max (input B U H : ℤ) (LightMomentDeterminant.wordBound (input B U H) H)≤lim.word :=
  (detector_word_bound (input B U H) H).trans hw
end ThreeSum.WeightedGlobalMomentDetectorResources
