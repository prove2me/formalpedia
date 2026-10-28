-- Prove2me | solution 1 for PCSPBLPAff.Symmetric.P_nonneg_sum
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:54:01.775799+00:00
-- url     : https://prove2.me/submissions/316c5b44-1885-4851-a2c4-1907513f993c

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

open PCSPBLPAff.Symmetric

theorem solution {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (X : Instance τ ar) (𝔸 : RelStruct τ ar A) (w : Fin X.n → A → ℚ)
    (p : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℚ) (r : Fin X.n → A → ℤ)
    (q : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℤ)
    (hLP : IsLPSol X 𝔸 w p) (hAff : IsAffSol X 𝔸 r q) (href : ∀ j y, p j y = 0 → q j y = 0)
    (ℓ : ℕ) (hℓ : 0 < ℓ) (hp : ∀ j y, ∃ z : ℤ, (ℓ : ℚ) * p j y = z)
    (M : ℕ) (hq : ∀ j y, |q j y| ≤ M)
    (u v L : ℕ) (hL : L = u * ℓ + v) (hv : v < ℓ) (hLM : M * ℓ ^ 2 ≤ L) :
    ∀ j, ∃ P : (Fin (ar (X.sym j)) → A) → ℕ,
      (∀ y, (P y : ℚ) = u * ℓ * p j y + v * q j y) ∧ ∑ y, P y = L := by
  intro j
  choose z hz using hp
  have hMu : M * ℓ ≤ u := by
    by_contra h
    push_neg at h
    have h2 : (u + 1) * ℓ ≤ M * ℓ * ℓ := Nat.mul_le_mul_right ℓ h
    nlinarith
  have hMuZ : (M : ℤ) * ℓ ≤ u := by exact_mod_cast hMu
  have hnn : ∀ a, 0 ≤ (u : ℤ) * z j a + v * q j a := by
    intro a
    by_cases hw0 : p j a = 0
    · have hr0 := href j a hw0
      have hz0 : z j a = 0 := by
        have := hz j a
        rw [hw0, mul_zero] at this
        exact_mod_cast this.symm
      rw [hr0, hz0]; simp
    · have hwpos : 0 < p j a := lt_of_le_of_ne (hLP.2.1 j a) (Ne.symm hw0)
      have hzpos : (0 : ℚ) < z j a := by
        rw [← hz j a]; exact mul_pos (by exact_mod_cast hℓ) hwpos
      have hz1 : 1 ≤ z j a := by exact_mod_cast hzpos
      have hra : -(M : ℤ) ≤ q j a := neg_le_of_abs_le (hq j a)
      have hvl : (v : ℤ) ≤ ℓ := by exact_mod_cast hv.le
      have hu0 : (0 : ℤ) ≤ u := by positivity
      have hv0 : (0 : ℤ) ≤ v := by positivity
      have hM0 : (0 : ℤ) ≤ M := by positivity
      have e1 : (v : ℤ) * M ≤ ℓ * M := mul_le_mul_of_nonneg_right hvl hM0
      have e2 : (u : ℤ) ≤ u * z j a := le_mul_of_one_le_right hu0 hz1
      have e3 : (v : ℤ) * (-(M : ℤ)) ≤ v * q j a := mul_le_mul_of_nonneg_left hra hv0
      nlinarith
  refine ⟨fun a => ((u : ℤ) * z j a + v * q j a).toNat, ?_, ?_⟩
  · intro a
    have h1 : ((((u : ℤ) * z j a + v * q j a).toNat : ℤ) : ℚ) = (((u : ℤ) * z j a + v * q j a : ℤ) : ℚ) := by
      rw [Int.toNat_of_nonneg (hnn a)]
    have h2 : ((((u : ℤ) * z j a + v * q j a).toNat : ℕ) : ℚ) = ((((u : ℤ) * z j a + v * q j a).toNat : ℤ) : ℚ) := by
      norm_cast
    rw [h2, h1]
    push_cast
    rw [← hz j a]
    ring
  · have hsum : ∀ a, ((((u : ℤ) * z j a + v * q j a).toNat : ℕ) : ℚ) = u * ℓ * p j a + v * q j a := by
      intro a
      have h1 : ((((u : ℤ) * z j a + v * q j a).toNat : ℤ) : ℚ) = (((u : ℤ) * z j a + v * q j a : ℤ) : ℚ) := by
        rw [Int.toNat_of_nonneg (hnn a)]
      have h2 : ((((u : ℤ) * z j a + v * q j a).toNat : ℕ) : ℚ) = ((((u : ℤ) * z j a + v * q j a).toNat : ℤ) : ℚ) := by
        norm_cast
      rw [h2, h1]
      push_cast
      rw [← hz j a]
      ring
    apply Nat.cast_injective (R := ℚ)
    rw [Nat.cast_sum]
    simp only [hsum]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hLP.2.2.2.2.1 j]
    have hr1 : (∑ a, (q j a : ℚ)) = 1 := by
      rw [← Int.cast_sum, hAff.2.2.1 j]; simp
    rw [hr1, hL]
    push_cast
    ring
