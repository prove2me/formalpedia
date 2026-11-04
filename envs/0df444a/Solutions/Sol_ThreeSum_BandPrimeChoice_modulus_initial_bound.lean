-- Prove2me | solution 1 for ThreeSum.BandPrimeChoice.modulus_initial_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:59:08.471194+00:00
-- url     : https://prove2.me/submissions/6d81cf86-cd02-465d-a83d-e85f2fda85e1

import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandPrimeChoice
import Definitions.Def_WeightedCache3SUM_Alias_111f6fe33c50551c
import Theorems.Thm_ThreeSum_BandWeightedScore_score_bound
import Theorems.Thm_ThreeSum_LightPrimeChain_modulus_score_bound
import Theorems.Thm_ThreeSum_PrimeChain_modulus_score_bound


set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeChoice
open BandCandidateRows BandWeightedScore Finset
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 8000
namespace ThreeSum.BandPrimeChoice
theorem _root_.solution (primes : ℕ → ℕ) (s nA nB nC g y U r : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ)) (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    s^r*score primes s (modulus primes s nA nB nC g A B C rs r) nA nB nC g A B C rs ≤
      (Nat.log y (3*U))^r*(rs.length*(s*g^3)) :=
  (modulus_score_bound primes s nA nB nC g y U r A B C rs hy hprime hinj hlo hA hB hC).trans
    (Nat.mul_le_mul_left _ (score_bound primes s 1 nA nB nC g A B C rs hprime hinj))
end ThreeSum.BandPrimeChoice
