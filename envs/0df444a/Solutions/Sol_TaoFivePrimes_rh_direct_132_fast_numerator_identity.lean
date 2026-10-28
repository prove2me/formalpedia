-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_132_fast_numerator_identity
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:49:24.555971+00:00
-- url     : https://prove2.me/submissions/972b0e93-5f82-4426-90d1-d6f56982c812

/- Equality of two exact integer presentations of the height-132 numerator. -/
import Definitions.Def_TaoFivePrimes_RHDirect132FastNumerator
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Finset

namespace Direct132FastNumeratorProof

lemma fast_choose_eq (n m : ℕ) : RHNextMomentInteger.fastChoose n m=Nat.choose n m := by
  by_cases h : m≤n
  · simp only [RHNextMomentInteger.fastChoose,if_pos h,Nat.choose_eq_factorial_div_factorial h]
  · simp only [RHNextMomentInteger.fastChoose,if_neg h,Nat.choose_eq_zero_of_lt (lt_of_not_ge h)]

lemma weight_eq (i k m : ℕ) :
    RHDirect132FastNumerator.weight i k m = RHDirect132CachedRule.weight i k m := by
  simp only [RHDirect132FastNumerator.weight,RHDirect132CachedRule.weight,fast_choose_eq]

lemma panelRe_eq (i k : ℕ) :
    RHDirect132FastNumerator.panelRe i k = RHDirect132CachedRule.panelRe i k := by
  unfold RHDirect132FastNumerator.panelRe RHDirect132CachedRule.panelRe
  simp_rw [weight_eq]

lemma panelIm_eq (i k : ℕ) :
    RHDirect132FastNumerator.panelIm i k = RHDirect132CachedRule.panelIm i k := by
  unfold RHDirect132FastNumerator.panelIm RHDirect132CachedRule.panelIm
  simp_rw [weight_eq]

lemma numeratorRe_eq (k : ℕ) :
    RHDirect132FastNumerator.numeratorRe k = RHDirect132CachedRule.numeratorRe k := by
  unfold RHDirect132FastNumerator.numeratorRe RHDirect132CachedRule.numeratorRe
  simp_rw [panelRe_eq,panelIm_eq]

lemma numeratorIm_eq (k : ℕ) :
    RHDirect132FastNumerator.numeratorIm k = RHDirect132CachedRule.numeratorIm k := by
  unfold RHDirect132FastNumerator.numeratorIm RHDirect132CachedRule.numeratorIm
  simp_rw [panelRe_eq,panelIm_eq]

end Direct132FastNumeratorProof

theorem solution (k : ℕ) :
    RHDirect132FastNumerator.component k =
      if k%2=0 then RHDirect132CachedRule.numeratorRe k
      else RHDirect132CachedRule.numeratorIm k := by
  simp only [RHDirect132FastNumerator.component,
    Direct132FastNumeratorProof.numeratorRe_eq,Direct132FastNumeratorProof.numeratorIm_eq]
