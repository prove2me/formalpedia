-- Prove2me | solution 1 for ThreeSum.BandPrimeScales.modulus_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:27:01.994216+00:00
-- url     : https://prove2.me/submissions/969f9312-e56e-4920-9a76-b590116fbecf

import Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Theorems.Thm_ThreeSum_BandPrimeChoice_modulus_bounds
import Theorems.Thm_ThreeSum_LightBandPrimeConstruction_modulus_bounds
import Theorems.Thm_ThreeSum_LightPrimeChain_modulus_bounds
import Theorems.Thm_ThreeSum_PrimeChain_modulus_bounds
import Theorems.Thm_ThreeSum_Scales_primeWindow_ge_two


set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeScales
open BandCandidateRows Scales BandScales CostLedger
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000
namespace ThreeSum.BandPrimeScales
theorem _root_.solution (n nA nB nC : ℕ) (A B C : ℕ → ℤ) (rs : List Record) :
    primeWindow n^primeDepth radix n ≤ modulus n nA nB nC A B C rs ∧
      modulus n nA nB nC A B C rs ≤ (4*primeWindow n)^primeDepth radix n :=
  LightBandPrimeConstruction.modulus_bounds A B C rs _ (by have := primeWindow_ge_two n; omega)
end ThreeSum.BandPrimeScales
