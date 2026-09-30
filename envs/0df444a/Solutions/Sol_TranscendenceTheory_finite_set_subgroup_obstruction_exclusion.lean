-- Prove2me | solution 1 for TranscendenceTheory.finite_set_subgroup_obstruction_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T15:43:37.873299+00:00
-- url     : https://prove2.me/submissions/179d2dc8-1454-4af2-b3ef-cb46cd7fcab9

import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section


private lemma p2m_quotient_image_ncard_mono
    (R A : Type*) [Ring R] [AddCommGroup A] [Module R A]
    (K Λ : Submodule R A) (hK : K ≤ Λ) (X : Finset A) :
    (Λ.mkQ '' (X : Set A)).ncard ≤ (K.mkQ '' (X : Set A)).ncard := by
  have himage : Λ.mkQ '' (X : Set A) =
      Submodule.factor hK '' (K.mkQ '' (X : Set A)) := by
    rw [Set.image_image]
    rfl
  rw [himage]
  exact Set.ncard_image_le (X.finite_toSet.image K.mkQ)

theorem solution
    (R A : Type*) [Ring R] [AddCommGroup A] [Module R A]
    (Λ : Submodule R A) (X : Finset A)
    (C : ℝ) (hC : 0 < C) (m n T : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hfirst : 3 * C * (m : ℝ) * (n : ℝ) ^ 2 < (T : ℝ) * X.card)
    (hsecond : 3 * C * (n : ℝ) ^ 2 <
      (T : ℝ) * (Λ.mkQ '' (X : Set A)).ncard)
    (K : Submodule R A) (a b : ℕ)
    (hprofile : (a = 1 ∧ K = ⊥) ∨ (a = 0 ∧ K ≤ Λ)) (hb : b ≤ 2) :
    C * (m : ℝ) ^ a * (n : ℝ) ^ b <
      ((T / 3 + 1 : ℕ) : ℝ) * (K.mkQ '' (X : Set A)).ncard := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnb : (n : ℝ) ^ b ≤ (n : ℝ) ^ 2 := pow_le_pow_right₀ hn' hb
  have hround_nat : T ≤ 3 * (T / 3 + 1) := by omega
  have hround : (T : ℝ) ≤ 3 * ((T / 3 + 1 : ℕ) : ℝ) := by
    exact_mod_cast hround_nat
  have hmult (N : ℕ) : (T : ℝ) * N ≤
      3 * (((T / 3 + 1 : ℕ) : ℝ) * N) := by
    nlinarith [mul_le_mul_of_nonneg_right hround (Nat.cast_nonneg (α := ℝ) N)]
  rcases hprofile with ⟨rfl, rfl⟩ | ⟨rfl, hK⟩
  · have hinj : Function.Injective (⊥ : Submodule R A).mkQ := by
      apply LinearMap.ker_eq_bot.mp
      exact Submodule.ker_mkQ _
    have hcard : ((⊥ : Submodule R A).mkQ '' (X : Set A)).ncard = X.card := by
      rw [Set.ncard_image_of_injective _ hinj]
      exact Set.ncard_coe_finset X
    rw [hcard, pow_one]
    have hdeg : C * (m : ℝ) * (n : ℝ) ^ b ≤ C * (m : ℝ) * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hnb (by positivity)
    nlinarith [hmult X.card]
  · rw [pow_zero, mul_one]
    have hcard : (Λ.mkQ '' (X : Set A)).ncard ≤ (K.mkQ '' (X : Set A)).ncard :=
      p2m_quotient_image_ncard_mono R A K Λ hK X
    have hcard' : ((Λ.mkQ '' (X : Set A)).ncard : ℝ) ≤
        (K.mkQ '' (X : Set A)).ncard := by exact_mod_cast hcard
    have hcount := mul_le_mul_of_nonneg_left hcard' (Nat.cast_nonneg (α := ℝ) T)
    have hdeg : C * (n : ℝ) ^ b ≤ C * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hnb hC.le
    nlinarith [hmult (K.mkQ '' (X : Set A)).ncard]

