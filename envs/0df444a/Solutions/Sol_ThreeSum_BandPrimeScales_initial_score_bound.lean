-- Prove2me | solution 1 for ThreeSum.BandPrimeScales.initial_score_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:27:25.379507+00:00
-- url     : https://prove2.me/submissions/9a17e7b5-d9a7-49c9-945a-439284f832ba

import Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Theorems.Thm_ThreeSum_BandWeightedScore_score_bound
import Theorems.Thm_ThreeSum_LightPrimePool_prime_injective
import Theorems.Thm_ThreeSum_LightPrimePool_prime_spec
import Theorems.Thm_ThreeSum_LightPrimePool_size_eq_card


set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeScales
open BandCandidateRows Scales BandScales CostLedger
set_option maxHeartbeats 1600000
set_option maxRecDepth 9000
namespace ThreeSum.BandPrimeScales
theorem _root_.solution {n nA nB nC : ℕ} (A B C : ℕ → ℤ) (rs : List Record)
    (hcount : rs.length ≤ 3*bandCount n^2) :
    score n 1 nA nB nC A B C rs ≤ candidateCount n*MassScales.rawTripleBound n := by
  have hh := BandWeightedScore.score_bound (LightPrimePool.prime (primeWindow n))
    (LightPrimePool.size (primeWindow n)) 1 nA nB nC (bandSize n) A B C rs
    (fun _ hi => (LightPrimePool.prime_spec hi).1)
    (fun _ hi _ hj heq => LightPrimePool.prime_injective hi hj heq)
  calc
    _ ≤ rs.length*(LightPrimePool.size (primeWindow n)*bandSize n^3) := hh
    _ ≤ (3*bandCount n^2)*(LightPrimePool.size (primeWindow n)*bandSize n^3) :=
      Nat.mul_le_mul_right _ hcount
    _ = _ := by rw [LightPrimePool.size_eq_card]; unfold candidateCount MassScales.rawTripleBound; ring
end ThreeSum.BandPrimeScales
