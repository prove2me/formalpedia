-- Prove2me | solution 1 for ThreeSum.BandRawA.finiteAll_weightedFalseCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:59:46.562717+00:00
-- url     : https://prove2.me/submissions/6bcb865f-4fd0-4b2d-a8fe-cf4092c073a5

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Theorems.Thm_ThreeSum_BandRawA_sum_finiteAllProducts
import Theorems.Thm_ThreeSum_BandRawA_all_weightedFalseCount


set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
namespace ThreeSum.BandRawA
theorem _root_.solution (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) :
    Arithmetic.weightedFalseCount (finiteAllProducts nA nB nC g rs)
      (fun t => C t.2.2.val-B t.2.1.val-valueAt nA g rs A t.1.val)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q=
      BandWeightedScore.score primes aux q nA nB nC g A B C rs := by
  rw [← all_weightedFalseCount primes aux q nA nB nC g A B C rs]
  unfold Arithmetic.weightedFalseCount
  exact sum_finiteAllProducts
    (fun t => if (q : ℤ) ∣ ModuloCounts.difference (valueAt nA g rs A) B C t then
      Arithmetic.missWeight (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux))
        (ModuloCounts.difference (valueAt nA g rs A) B C t) else 0) nA nB nC g rs
end ThreeSum.BandRawA
