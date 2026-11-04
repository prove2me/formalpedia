-- Prove2me | solution 1 for ThreeSum.EncodedColorNormalizedData.incidences_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:06:51.849592+00:00
-- url     : https://prove2.me/submissions/4b1fa4d2-f855-4f96-80e0-dc10f5e29506

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Definitions.Def_Submission_ThreeSum_EncodedColorParameterData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorNormalizedData
import Theorems.Thm_ThreeSum_BandRawA_values_bounded
import Definitions.Def_WeightedCache3SUM_Alias_f8621e0ea40777d9


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorNormalizedData
open Light Scales BandScales ColorClassLists BandRawA EncodedColorLayout
namespace ThreeSum.EncodedColorNormalizedData
theorem _root_.solution {A B C : List ℤ} {n U : ℕ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hA : ∀ j < A.length, |A.getD j 0| ≤ (U : ℤ)) :
    ∀ z ∈ incidences n A B C hsA hsB hsC, |z| ≤ (U : ℤ) := values_bounded hA
end ThreeSum.EncodedColorNormalizedData
