-- Prove2me | solution 1 for ThreeSum.BandRawA.finiteOwner_weightedFalseCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:54:23.910208+00:00
-- url     : https://prove2.me/submissions/bd78f557-c6ea-4522-aed7-78e772be590c

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Theorems.Thm_ThreeSum_BandRawA_sum_finiteOwnerProduct
import Theorems.Thm_Light_Ends_block
import Definitions.Def_WeightedCache3SUM_Alias_14da40ac2f123923


set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000
namespace ThreeSum.BandRawA
theorem _root_.solution (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) {s : ℕ} (hs : s < rs.length) :
    Arithmetic.weightedFalseCount (finiteOwnerProduct nA nB nC g rs s)
      (fun t => C t.2.2.val-B t.2.1.val-valueAt nA g rs A t.1.val)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q=
      BandWeightedScore.block primes aux q nA nB nC g A B C (rs.getD s default) := by
  rw [← owner_weightedFalseCount primes aux q nA nB nC g A B C rs hs]
  unfold Arithmetic.weightedFalseCount
  exact sum_finiteOwnerProduct
    (fun t => if (q : ℤ) ∣ ModuloCounts.difference (valueAt nA g rs A) B C t then
      Arithmetic.missWeight (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux))
        (ModuloCounts.difference (valueAt nA g rs A) B C t) else 0) nA nB nC g rs hs
end ThreeSum.BandRawA
