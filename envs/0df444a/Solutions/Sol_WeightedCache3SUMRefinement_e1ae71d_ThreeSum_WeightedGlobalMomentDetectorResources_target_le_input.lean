-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentDetectorResources.target_le_input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:29:59.58613+00:00
-- url     : https://prove2.me/submissions/129ad799-81e1-4ab7-b1c0-9b57ed5d9f92

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentDetectorResources

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentDetectorResources
open WeightedGlobalNativeMomentBounds StageBounds
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentDetectorResources
theorem _root_.solution (B U H : ℕ) (x : ℤ) (hx : |x|≤(U : ℤ)) :
    |x|≤(input B U H : ℤ) :=
  hx.trans (by exact_mod_cast (Nat.le_add_right U (B*(2*U+1)^(2*H))))
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentDetectorResources
