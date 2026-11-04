-- Prove2me | solution 1 for ThreeSum.WeightedGlobalMomentDetectorResources.target_le_input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:31:00.357282+00:00
-- url     : https://prove2.me/submissions/8eea2bde-116b-4c9d-8859-1ffbc1d27aac

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_Weighted_Global_TernaryMomentDetectorResources

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentDetectorResources
open WeightedGlobalNativeMomentBounds StageBounds
namespace ThreeSum.WeightedGlobalMomentDetectorResources
theorem _root_.solution (B U H : ℕ) (x : ℤ) (hx : |x|≤(U : ℤ)) :
    |x|≤(input B U H : ℤ) :=
  hx.trans (by exact_mod_cast (Nat.le_add_right U (B*(2*U+1)^(2*H))))
end ThreeSum.WeightedGlobalMomentDetectorResources
