-- Prove2me | solution 1 for ThreeSum.BandPrimeChoice.modulus_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:12:55.866233+00:00
-- url     : https://prove2.me/submissions/11f89aab-0015-44e8-8f53-3917c5eda600

import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandPrimeChoice
import Theorems.Thm_ThreeSum_BandPrimeChoice_modulus_bounds
import Theorems.Thm_ThreeSum_LightPrimeChain_modulus_bounds
import Theorems.Thm_ThreeSum_PrimeChain_modulus_bounds


set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeChoice
open BandCandidateRows BandWeightedScore Finset
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 8000
namespace ThreeSum.BandPrimeChoice
theorem _root_.solution (primes : ℕ → ℕ) {s nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (hs : 0 < s)
    (hprime : ∀ i < s, Nat.Prime (primes i)) (r : ℕ) :
    0 < modulus primes s nA nB nC g A B C rs r := by
  have hh := (modulus_bounds (nA := nA) (nB := nB) (nC := nC) (g := g) primes A B C rs hs 1
    (Finset.sup (range s) primes) r
    (fun i hi => (hprime i hi).pos)
    (fun i hi => Finset.le_sup (mem_range.mpr hi))).1
  rw [one_pow] at hh
  omega
end ThreeSum.BandPrimeChoice
