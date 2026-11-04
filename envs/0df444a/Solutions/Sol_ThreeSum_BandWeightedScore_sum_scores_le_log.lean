-- Prove2me | solution 1 for ThreeSum.BandWeightedScore.sum_scores_le_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:37.968425+00:00
-- url     : https://prove2.me/submissions/e176896e-1d3c-4fb3-9e5e-597112020d50

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightPrimeChain
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Theorems.Thm_ThreeSum_BandWeightedScore_sum_blocks_le_log

set_option autoImplicit false
open ThreeSum ThreeSum.BandWeightedScore
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
namespace ThreeSum.BandWeightedScore
theorem _root_.solution (primes : ℕ → ℕ) (s q nA nB nC g y U : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ)) (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    (∑ i ∈ range s, score primes s (q*primes i) nA nB nC g A B C rs) ≤
      Nat.log y (3*U)*score primes s q nA nB nC g A B C rs := by
  unfold score partialScore
  rw [sum_comm,mul_sum]
  exact sum_le_sum fun i _ => sum_blocks_le_log primes s q nA nB nC g y U A B C _
    hy hprime hinj hlo hA hB hC
end ThreeSum.BandWeightedScore
