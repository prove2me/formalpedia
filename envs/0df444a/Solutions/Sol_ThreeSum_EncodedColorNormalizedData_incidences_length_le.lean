-- Prove2me | solution 1 for ThreeSum.EncodedColorNormalizedData.incidences_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:27:04.219499+00:00
-- url     : https://prove2.me/submissions/b5d9e605-7dde-41ab-96a1-a6a4048e37ba

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Definitions.Def_Submission_ThreeSum_EncodedColorParameterData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorNormalizedData
import Theorems.Thm_ThreeSum_EncodedColorNormalizedData_records_length_le
import Theorems.Thm_ThreeSum_BandRawA_items_length_le
import Theorems.Thm_ThreeSum_BandRawA_values_length
import Theorems.Thm_ThreeSum_LightClassFilter_items_length_le
import Theorems.Thm_ThreeSum_RadixKeyLists_values_length


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorNormalizedData
open Light Scales BandScales ColorClassLists BandRawA EncodedColorLayout
namespace ThreeSum.EncodedColorNormalizedData
theorem _root_.solution {A B C : List ℤ} {n : ℕ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (ha : A.length ≤ n) (hb : B.length ≤ n) (hc : C.length ≤ n) :
    (incidences n A B C hsA hsB hsC).length ≤ bandSize n*ColorBandBounds.count n (bandSize n) := by
  unfold incidences
  rw [values_length]
  exact (items_length_le ..).trans (Nat.mul_le_mul_left _ (records_length_le ha hb hc))
end ThreeSum.EncodedColorNormalizedData
