-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.exists_chiP_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:20:22.185569+00:00
-- url     : https://prove2.me/submissions/a8c4da72-ca3b-4f91-ad6f-491ac162ef34

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_card_adt_le
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_chiPAux_neg_log_monoNormSq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Finset
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (D : ℕ) : ∃ C : ℝ, ∀ n : ℕ, chiP D n ≤ C * (n : ℝ) ^ (D + 1) := by
  obtain ⟨K, hKe⟩ : ∃ K : ℝ, K = Real.log ((D : ℝ) + 1) + D * (1 + D) := ⟨_, rfl⟩
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hK : 0 ≤ K := by
    have h1 : 0 ≤ Real.log ((D : ℝ) + 1) := Real.log_nonneg (by linarith)
    have h2 : (0 : ℝ) ≤ D * (1 + D) := by positivity
    rw [hKe]
    linarith
  refine ⟨2 ^ D * K, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hz : chiP D 0 = 0 := by
      unfold chiP
      have hsum0 : ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) 0, Real.log (monoNormSq a) = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        have hs := Finset.Nat.mem_antidiagonalTuple.mp ha
        have hz : ∀ i, a i = 0 := fun i => (Finset.sum_eq_zero_iff.mp hs) i (Finset.mem_univ i)
        have hm : monoNormSq a = 1 := by
          unfold monoNormSq
          rw [hs]
          simp only [hz, Nat.factorial_zero, Finset.prod_const_one, Nat.cast_one, one_mul, zero_add]
          exact div_self (by exact_mod_cast Nat.factorial_ne_zero D)
        rw [hm, Real.log_one]
      rw [hsum0]
      ring
    rw [hz]
    simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) ≤ n := by linarith
    have hterm : ∀ a ∈ Finset.Nat.antidiagonalTuple (D + 1) n, -Real.log (monoNormSq a) ≤ n * K := by
      intro a ha
      have hs := Finset.Nat.mem_antidiagonalTuple.mp ha
      have h1 := chiPAux_neg_log_monoNormSq_le a
      rw [hs] at h1
      have hlog : Real.log ((n : ℝ) + D) ≤ (n : ℝ) + D := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n : ℝ) + D by linarith)
        linarith
      have h2 : (D : ℝ) * Real.log ((n : ℝ) + D) ≤ D * ((n : ℝ) + D) := mul_le_mul_of_nonneg_left hlog hD0
      have h3 : (D : ℝ) * ((n : ℝ) + D) ≤ n * (D * (1 + D)) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sq_nonneg (D : ℝ))]
      rw [hKe]
      linarith
    have hsum : chiP D n ≤ (1 / 2) * (((Finset.Nat.antidiagonalTuple (D + 1) n).card : ℝ) * (n * K)) := by
      unfold chiP
      have h := Finset.sum_le_sum hterm
      rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_neg_distrib] at h
      linarith
    have hcard : ((Finset.Nat.antidiagonalTuple (D + 1) n).card : ℝ) ≤ 2 ^ D * (n : ℝ) ^ D := by
      have h1 : ((Finset.Nat.antidiagonalTuple (D + 1) n).card : ℝ) ≤ ((n : ℝ) + 1) ^ D := by
        exact_mod_cast chiPAux_card_adt_le D n
      have h2 : ((n : ℝ) + 1) ^ D ≤ (2 * (n : ℝ)) ^ D := by
        gcongr
        linarith
      rw [mul_pow] at h2
      linarith
    have hnK : 0 ≤ (n : ℝ) * K := mul_nonneg hn0 hK
    have hc0 : (0 : ℝ) ≤ ((Finset.Nat.antidiagonalTuple (D + 1) n).card : ℝ) := Nat.cast_nonneg _
    calc chiP D n ≤ (1 / 2) * (((Finset.Nat.antidiagonalTuple (D + 1) n).card : ℝ) * (n * K)) := hsum
      _ ≤ ((Finset.Nat.antidiagonalTuple (D + 1) n).card : ℝ) * (n * K) := by
          linarith [mul_nonneg hc0 hnK]
      _ ≤ (2 ^ D * (n : ℝ) ^ D) * (n * K) := mul_le_mul_of_nonneg_right hcard hnK
      _ = 2 ^ D * K * (n : ℝ) ^ (D + 1) := by ring
end ReciprocityTheory.GeometryOfNumbersTheory
