-- Prove2me | solution 1 for ThreeSum.EncodedColorPrimeCosts.moduli_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:39:45.089623+00:00
-- url     : https://prove2.me/submissions/6f1ff9ad-ba8b-4373-8e4f-79f6a500e6fd

import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrime
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeCosts
import Theorems.Thm_ThreeSum_BandPrimeChoice_modulus_pos
import Theorems.Thm_ThreeSum_BlockSourceEncoding_modulus_pos
import Theorems.Thm_ThreeSum_LightPrimeChain_modulus_pos
import Theorems.Thm_ThreeSum_LightPrimePool_prime_spec
import Theorems.Thm_ThreeSum_LightPrimePool_size_pos


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorPrimeCosts
open Light Scales BandScales CostLedger ArithmeticStageBounds
namespace ThreeSum.EncodedColorPrimeCosts
theorem _root_.solution {A B C : List ℤ} {g y : ℕ} {hg : 0 < g}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hy : 0 < y) (i : ℕ) : 0 < LightEncodedColorPrime.moduli A B C g hg hsA hsB hsC y i :=
  BandPrimeChoice.modulus_pos (LightPrimePool.prime y)
    (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
    (BandRawA.sortedRecords A B C g hg hsA hsB hsC) (LightPrimePool.size_pos hy)
    (fun j hj => (LightPrimePool.prime_spec hj).1) i
end ThreeSum.EncodedColorPrimeCosts
