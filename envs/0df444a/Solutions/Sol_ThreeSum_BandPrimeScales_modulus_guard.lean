-- Prove2me | solution 1 for ThreeSum.BandPrimeScales.modulus_guard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:31:31.84343+00:00
-- url     : https://prove2.me/submissions/edaac521-d282-484e-90bb-7d9a184f69bb

import Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Theorems.Thm_ThreeSum_BandPrimeScales_modulus_bounds
import Theorems.Thm_ThreeSum_BandPrimeChoice_modulus_bounds
import Theorems.Thm_ThreeSum_LightBandPrimeConstruction_modulus_bounds
import Theorems.Thm_ThreeSum_LightPrimeChain_modulus_bounds
import Theorems.Thm_ThreeSum_PrimeChain_modulus_bounds
import Theorems.Thm_ThreeSum_Scales_primeDepth_upper


set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeScales
open BandCandidateRows Scales BandScales CostLedger
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000
namespace ThreeSum.BandPrimeScales
theorem _root_.solution {n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List Record)
    (hR : 4 ≤ radix n) : 4*modulus n nA nB nC A B C rs ≤ radix n :=
  (Nat.mul_le_mul_left 4 (modulus_bounds n nA nB nC A B C rs).2).trans
    (primeDepth_upper radix hR)
end ThreeSum.BandPrimeScales
