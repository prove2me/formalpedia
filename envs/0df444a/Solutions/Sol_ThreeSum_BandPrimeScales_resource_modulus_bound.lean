-- Prove2me | solution 1 for ThreeSum.BandPrimeScales.resource_modulus_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:50:55.727196+00:00
-- url     : https://prove2.me/submissions/c31d48f7-cb97-43ed-b0df-7c5f1fd917fb

import Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Theorems.Thm_ThreeSum_Scales_primeDepth_upper


set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeScales
open BandCandidateRows Scales BandScales CostLedger
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000
namespace ThreeSum.BandPrimeScales
theorem _root_.solution {n : ℕ} (hR : 4 ≤ radix n) :
    (4*primeWindow n)^(primeDepth radix n+1) ≤ ArithmeticStageBounds.maxMod n := by
  have hh := primeDepth_upper radix hR
  have hp : (4*primeWindow n)^primeDepth radix n ≤ radix n := by omega
  rw [pow_succ]
  exact Nat.mul_le_mul hp (Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) _)
end ThreeSum.BandPrimeScales
