-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentDetectorResources.word_guard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:38:42.111795+00:00
-- url     : https://prove2.me/submissions/f1462074-377f-4553-ad46-784dcc2ef668

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentDetectorResources
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeMomentBounds_detector_word_bound


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentDetectorResources
open WeightedGlobalNativeMomentBounds StageBounds
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentDetectorResources
theorem _root_.solution (B U H : ℕ) (lim : Light.Limits)
    (hw : ((need B U H).word : ℤ)≤lim.word) :
    max (input B U H : ℤ) (LightMomentDeterminant.wordBound (input B U H) H)≤lim.word :=
  (detector_word_bound (input B U H) H).trans hw
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentDetectorResources
