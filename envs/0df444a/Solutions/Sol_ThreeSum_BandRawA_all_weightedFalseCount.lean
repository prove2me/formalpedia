-- Prove2me | solution 1 for ThreeSum.BandRawA.all_weightedFalseCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:45:37.452401+00:00
-- url     : https://prove2.me/submissions/939bbc3c-82e8-4b71-a742-f92e42ea30b2

import Definitions.Def_Submission_ThreeSum_BandRawAProduct
import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_WeightedCache3SUM_Alias_14da40ac2f123923
import Theorems.Thm_ThreeSum_BandRawA_sum_allProducts


set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000
namespace ThreeSum.BandRawA
theorem _root_.solution (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) :
    Arithmetic.weightedFalseCount (allProducts nA nB nC g rs)
      (ModuloCounts.difference (valueAt nA g rs A) B C)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q=
      BandWeightedScore.score primes aux q nA nB nC g A B C rs := by
  unfold Arithmetic.weightedFalseCount
  rw [sum_allProducts]
  unfold BandWeightedScore.score BandWeightedScore.partialScore
  apply sum_congr rfl
  intro s hs
  exact owner_weightedFalseCount primes aux q nA nB nC g A B C rs (mem_range.mp hs)
end ThreeSum.BandRawA
