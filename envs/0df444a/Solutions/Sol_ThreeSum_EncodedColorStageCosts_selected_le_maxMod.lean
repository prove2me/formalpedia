-- Prove2me | solution 1 for ThreeSum.EncodedColorStageCosts.selected_le_maxMod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:37:20.223182+00:00
-- url     : https://prove2.me/submissions/b5ed9ff1-5e74-41d3-abad-54ada60f18db

import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Theorems.Thm_ThreeSum_EncodedColorPrimeReadyData_selected_guard
import Theorems.Thm_ThreeSum_Scales_primeWindow_ge_two


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorStageCosts
open Scales BandScales ArithmeticStageBounds
namespace ThreeSum.EncodedColorStageCosts
theorem _root_.solution {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hR : 4 ≤ radix n) : EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC ≤ maxMod n := by
  have hp := EncodedColorPrimeReadyData.selected_guard (A := A) (B := B) (C := C)
    (hsA := hsA) (hsB := hsB) (hsC := hsC) hR
  have hy := primeWindow_ge_two n
  have hm : radix n ≤ maxMod n := by
    unfold maxMod
    exact Nat.le_mul_of_pos_right _ (by positivity)
  omega
end ThreeSum.EncodedColorStageCosts
