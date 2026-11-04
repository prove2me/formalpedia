-- Prove2me | solution 1 for ThreeSum.BandRawA.physical_weighted_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:53:07.909665+00:00
-- url     : https://prove2.me/submissions/469ee2f5-4afe-44e7-9f80-2714b91c0701

import Definitions.Def_Submission_ThreeSum_BandRawAProduct
import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Theorems.Thm_ThreeSum_BandRawA_all_weightedFalseCount
import Theorems.Thm_ThreeSum_BandWeightedScore_score_bound


set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000
namespace ThreeSum.BandRawA
theorem _root_.solution (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record)
    (hprime : ∀ i < aux, Nat.Prime (primes i))
    (hinj : ∀ i < aux, ∀ j < aux, primes i=primes j → i=j) :
    Arithmetic.weightedFalseCount (allProducts nA nB nC g rs)
      (ModuloCounts.difference (valueAt nA g rs A) B C)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q ≤ rs.length*(aux*g^3) := by
  rw [all_weightedFalseCount]
  exact BandWeightedScore.score_bound primes aux q nA nB nC g A B C rs hprime hinj
end ThreeSum.BandRawA
