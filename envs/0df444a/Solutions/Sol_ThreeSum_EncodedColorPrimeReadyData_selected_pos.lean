-- Prove2me | solution 1 for ThreeSum.EncodedColorPrimeReadyData.selected_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:14:33.581322+00:00
-- url     : https://prove2.me/submissions/566b3d80-ea2e-4e0b-b2e0-4daf8883651f

import Definitions.Def_Submission_ThreeSum_EncodedColorNormalizedData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Theorems.Thm_ThreeSum_EncodedColorPrimeCosts_moduli_pos
import Theorems.Thm_ThreeSum_Scales_primeWindow_ge_two


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorPrimeReadyData
open Light Scales BandScales ColorClassLists EncodedColorLayout EncodedColorNormalizedData
namespace ThreeSum.EncodedColorPrimeReadyData
theorem _root_.solution {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} :
    0 < selected n A B C hsA hsB hsC :=
  EncodedColorPrimeCosts.moduli_pos (lt_of_lt_of_le (by decide : 0 < 2) (primeWindow_ge_two n)) _
end ThreeSum.EncodedColorPrimeReadyData
