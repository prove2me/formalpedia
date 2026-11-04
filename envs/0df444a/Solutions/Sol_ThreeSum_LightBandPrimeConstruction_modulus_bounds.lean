-- Prove2me | solution 1 for ThreeSum.LightBandPrimeConstruction.modulus_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:19:45.741006+00:00
-- url     : https://prove2.me/submissions/44caecf3-6b4d-4d84-ba7e-af0aca485a6e

import Definitions.Def_Submission_ThreeSum_LightBandPrimeChain
import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
import Theorems.Thm_ThreeSum_BandPrimeChoice_modulus_bounds
import Theorems.Thm_ThreeSum_LightPrimeChain_modulus_bounds
import Theorems.Thm_ThreeSum_LightPrimePool_prime_spec
import Theorems.Thm_ThreeSum_LightPrimePool_size_pos
import Theorems.Thm_ThreeSum_PrimeChain_modulus_bounds


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeConstruction
open Light BandCandidateRows
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
namespace ThreeSum.LightBandPrimeConstruction
theorem _root_.solution {y nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (levels : ℕ) (hy : 0 < y) :
    y^levels ≤ modulus y nA nB nC g A B C rs levels ∧
      modulus y nA nB nC g A B C rs levels ≤ (4*y)^levels :=
  BandPrimeChoice.modulus_bounds (LightPrimePool.prime y) A B C rs
    (LightPrimePool.size_pos hy) y (4*y) levels
    (fun i hi => (LightPrimePool.prime_spec hi).2.1.le)
    (fun i hi => (LightPrimePool.prime_spec hi).2.2)
end ThreeSum.LightBandPrimeConstruction
