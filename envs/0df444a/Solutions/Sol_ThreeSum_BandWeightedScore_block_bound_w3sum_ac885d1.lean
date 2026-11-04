-- Prove2me | solution 1 for ThreeSum.BandWeightedScore.block_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:07:31.729985+00:00
-- url     : https://prove2.me/submissions/5af75973-b27c-4abb-946a-090741eff828

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightPrimeChain
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Theorems.Thm_ThreeSum_BandWeightedScore_length_le
import Theorems.Thm_Light_Ends_block
import Theorems.Thm_ThreeSum_BandPartition_length_le
import Theorems.Thm_ThreeSum_WeightedScore_remaining_le
import Definitions.Def_WeightedCache3SUM_Alias_31b4729195398428


set_option autoImplicit false
open ThreeSum ThreeSum.BandWeightedScore
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
namespace ThreeSum.BandWeightedScore
theorem _root_.solution (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (r : Record)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j) :
    block primes s q nA nB nC g A B C r ≤ s*g^3 := by
  unfold block
  split_ifs
  · rw [WeightedScore.score_eq_remaining _ _ _ _ _ _ _ _ _ hprime hinj]
    have hh := WeightedScore.remaining_le primes s q (length nA g r.a)
      (length nB g r.b) (length nC g r.c)
      (fun i => A (r.a*g+i)) (fun i => B (r.b*g+i)) (fun i => C (r.c*g+i)) s
    have hp : length nA g r.a*length nB g r.b*length nC g r.c ≤ g^3 := by
      calc
        _ ≤ g*g*g := Nat.mul_le_mul (Nat.mul_le_mul (length_le ..) (length_le ..)) (length_le ..)
        _ = _ := by ring
    exact hh.trans (Nat.mul_le_mul_left s hp)
  · omega
end ThreeSum.BandWeightedScore
