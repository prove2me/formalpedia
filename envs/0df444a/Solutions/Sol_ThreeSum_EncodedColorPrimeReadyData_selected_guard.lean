-- Prove2me | solution 1 for ThreeSum.EncodedColorPrimeReadyData.selected_guard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:27:28.054492+00:00
-- url     : https://prove2.me/submissions/0d28dedd-0f08-43cc-bb91-af5dd56e8a2c

import Definitions.Def_Submission_ThreeSum_EncodedColorNormalizedData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Theorems.Thm_ThreeSum_EncodedColorPrimeCosts_scheduled_modulus_guard


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorPrimeReadyData
open Light Scales BandScales ColorClassLists EncodedColorLayout EncodedColorNormalizedData
namespace ThreeSum.EncodedColorPrimeReadyData
theorem _root_.solution {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hR : 4 ≤ radix n) : 4*selected n A B C hsA hsB hsC ≤ radix n :=
  EncodedColorPrimeCosts.scheduled_modulus_guard hR
end ThreeSum.EncodedColorPrimeReadyData
