-- Prove2me | solution 1 for ThreeSum.LightPrimeChain.sum_scores_le_log_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:23:37.151229+00:00
-- url     : https://prove2.me/submissions/9ca239f5-9a36-4b7c-96e7-4b92c42b0ad1

import Definitions.Def_Submission_ThreeSum_LightPrimeMinimum
import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_LightPrimeChain
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_PrimeChain_score_eq_weightedFalseCount
import Theorems.Thm_ThreeSum_PrimeChain_sum_scores_le_log
import Theorems.Thm_ThreeSum_WeightedScore_corrections_zero
import Theorems.Thm_ThreeSum_WeightedScore_remaining_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.WeightedScore.corrections_zero
attribute [local simp] ThreeSum.WeightedScore.remaining_zero



set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimeChain
open Light WeightedScore LightPrimeMinimum Finset
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightPrimeChain
theorem _root_.solution (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (A B C : ℕ → ℤ) (y M : ℕ) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hbound : ∀ t ∈ ModuloCounts.triples nA nB nC,
      (ModuloCounts.difference A B C t).natAbs ≤ M) :
    (∑ i ∈ range s, score primes s (q*primes i) nA nB nC A B C) ≤
      Nat.log y M * score primes s q nA nB nC A B C := by
  let pool := auxiliarySet primes s
  have hpr : ∀ p ∈ pool, Nat.Prime p := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    exact hprime i (mem_range.mp hi)
  have hlow : ∀ p ∈ pool, y ≤ p := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    exact hlo i (mem_range.mp hi)
  have hsum : (∑ i ∈ range s, score primes s (q*primes i) nA nB nC A B C) =
      ∑ p ∈ pool, score primes s (q*p) nA nB nC A B C := by
    symm
    unfold pool auxiliarySet
    rw [sum_image]
    intro i hi j hj heq
    exact hinj i (mem_range.mp hi) j (mem_range.mp hj) heq
  rw [hsum]
  have havg := PrimeChain.sum_scores_le_log (ModuloCounts.triples nA nB nC)
    (ModuloCounts.difference A B C) (Arithmetic.missWeight (Auxiliary.moduli pool))
    (Arithmetic.missWeight_zero _) pool q y M hy hpr hlow hbound
  simpa only [PrimeChain.score_eq_weightedFalseCount,score,pool] using havg
end ThreeSum.LightPrimeChain
