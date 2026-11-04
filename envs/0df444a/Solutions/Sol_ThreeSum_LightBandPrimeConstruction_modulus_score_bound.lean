-- Prove2me | solution 1 for ThreeSum.LightBandPrimeConstruction.modulus_score_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:55:09.053179+00:00
-- url     : https://prove2.me/submissions/985a7184-148a-4344-a656-1ee41aaaee90

import Definitions.Def_Submission_ThreeSum_LightBandPrimeChain
import Definitions.Def_Submission_ThreeSum_LightPrimePool
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
import Definitions.Def_WeightedCache3SUM_Alias_111f6fe33c50551c
import Theorems.Thm_ThreeSum_LightPrimeChain_modulus_score_bound
import Theorems.Thm_ThreeSum_LightPrimePool_prime_injective
import Theorems.Thm_ThreeSum_LightPrimePool_prime_spec
import Theorems.Thm_ThreeSum_PrimeChain_modulus_score_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeConstruction
open Light BandCandidateRows
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
namespace ThreeSum.LightBandPrimeConstruction
theorem _root_.solution {y nA nB nC g U : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (levels : ℕ) (hy : 1 < y)
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ))
    (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    (LightPrimePool.size y)^levels * BandWeightedScore.score
      (LightPrimePool.prime y) (LightPrimePool.size y)
      (modulus y nA nB nC g A B C rs levels) nA nB nC g A B C rs ≤
      (Nat.log y (3*U))^levels * BandWeightedScore.score
        (LightPrimePool.prime y) (LightPrimePool.size y) 1 nA nB nC g A B C rs :=
  BandPrimeChoice.modulus_score_bound (LightPrimePool.prime y) (LightPrimePool.size y)
    nA nB nC g y U levels A B C rs hy (fun i hi => (LightPrimePool.prime_spec hi).1)
    (fun i hi j hj heq => LightPrimePool.prime_injective hi hj heq)
    (fun i hi => (LightPrimePool.prime_spec hi).2.1.le) hA hB hC
end ThreeSum.LightBandPrimeConstruction
