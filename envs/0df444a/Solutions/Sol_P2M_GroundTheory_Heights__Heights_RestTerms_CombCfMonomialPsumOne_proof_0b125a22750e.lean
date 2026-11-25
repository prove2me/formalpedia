-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombCfMonomialPsumOne_proof_0b125a22750e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:37:44.753358+00:00
-- url     : https://prove2.me/submissions/eba948a5-cf5c-4a9e-a363-803acc6317b4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombCfMonomialPsumOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CombCfMonomialPsumOne_sum_update_sub_one_1c80aec9c4ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CombCfMonomialPsumOne_prod_factorial_update_sub_one_5ed83b2dd899
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_zero_8589bd36c748
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_monomial_c1481e7819e6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_cf_mul_psum_0f698be248eb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset Comb
open CombCfMonomialPsumOne
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CombCfMonomialPsumOne
theorem _root_.solution : CombCfMonomialPsumOne.Statement := by
  intro m n v l
  induction n generalizing l with
  | zero =>
    rw [pow_zero, mul_one, cf_monomial]
    by_cases h : l = v
    · subst h; simp
    · rw [if_neg h, if_neg]
      rintro ⟨hle, hs⟩
      apply h
      funext i
      have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun i _ => hle i)).1
        (by simpa using hs.symm)
      exact (this i (Finset.mem_univ _)).symm
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, cf_mul_psum]
    simp only [ih]
    by_cases hC : (∀ i, v i ≤ l i) ∧ ∑ i, l i = ∑ i, v i + (n + 1)
    · rw [if_pos hC]
      obtain ⟨hle, hs⟩ := hC
      have hP : (∏ j, ((l j - v j).factorial : ℚ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun j _ => by positivity
      rw [Finset.sum_congr rfl (g := fun i => (n.factorial : ℚ) * ((l i - v i : ℕ) : ℚ) /
          ∏ j, ((l j - v j).factorial : ℚ)) ?_]
      · rw [← Finset.sum_div, ← Finset.mul_sum, ← Nat.cast_sum]
        have hsub : ∑ i, (l i - v i) + ∑ i, v i = ∑ i, l i := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hle i)
        rw [show ∑ i, (l i - v i) = n + 1 by omega, Nat.factorial_succ]
        push_cast
        ring
      · intro i _
        by_cases hi : v i < l i
        · have h1 : 1 ≤ l i := by omega
          have hle' : ∀ j, v j ≤ Function.update l i (l i - 1) j := fun j => by
            by_cases hj : j = i
            · subst hj; simp; omega
            · simp [Function.update_of_ne hj, hle j]
          have hs' := sum_update_sub_one l i h1
          rw [if_pos h1, if_pos ⟨hle', by omega⟩, ← prod_factorial_update_sub_one l v i hi]
          have hne : ((l i - v i : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : l i - v i ≠ 0)
          have hQ : (∏ j, ((Function.update l i (l i - 1) j - v j).factorial : ℚ)) ≠ 0 :=
            Finset.prod_ne_zero_iff.2 fun j _ => by positivity
          field_simp
        · have heq : l i = v i := le_antisymm (not_lt.1 hi) (hle i)
          rw [show ((l i - v i : ℕ) : ℚ) = 0 by rw [heq]; simp, mul_zero, zero_div]
          by_cases h1 : 1 ≤ l i
          · rw [if_pos h1, if_neg]
            rintro ⟨h, _⟩
            have := h i
            simp at this
            omega
          · rw [if_neg h1]
    · rw [if_neg hC]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases h1 : 1 ≤ l i
      · rw [if_pos h1]
        by_cases h2 : (∀ j, v j ≤ Function.update l i (l i - 1) j) ∧
            ∑ j, Function.update l i (l i - 1) j = ∑ j, v j + n
        · exfalso
          apply hC
          obtain ⟨hle', hs'⟩ := h2
          have hle : ∀ j, v j ≤ l j := fun j => (hle' j).trans (by
            by_cases hj : j = i
            · subst hj; simp
            · simp [Function.update_of_ne hj])
          have := sum_update_sub_one l i h1
          exact ⟨hle, by omega⟩
        · rw [if_neg h2]
      · rw [if_neg h1]
end CombCfMonomialPsumOne
end GroundTheory.Heights₂.Heights.RestTerms
