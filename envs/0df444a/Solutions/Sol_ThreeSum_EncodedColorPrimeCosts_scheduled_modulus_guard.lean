-- Prove2me | solution 1 for ThreeSum.EncodedColorPrimeCosts.scheduled_modulus_guard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:14:39.300726+00:00
-- url     : https://prove2.me/submissions/afb6ef2b-b9fe-4ecc-9078-54544c5d534f

import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrime
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeCosts
import Theorems.Thm_ThreeSum_EncodedColorPrimeCosts_scheduled_modulus_eq
import Theorems.Thm_ThreeSum_BandPrimeScales_modulus_guard
import Theorems.Thm_ThreeSum_BandScales_bandSize_pos


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorPrimeCosts
open Light Scales BandScales CostLedger ArithmeticStageBounds
namespace ThreeSum.EncodedColorPrimeCosts
theorem _root_.solution {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hR : 4 ≤ radix n) :
    4*LightEncodedColorPrime.moduli A B C (bandSize n) (bandSize_pos n) hsA hsB hsC (primeWindow n)
      (LightBandPrimeDepth.depth (radix n) (primeWindow n)) ≤ radix n := by
  rw [scheduled_modulus_eq]
  exact BandPrimeScales.modulus_guard _ _ _ _ hR
end ThreeSum.EncodedColorPrimeCosts
