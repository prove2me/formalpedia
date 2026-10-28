-- Prove2me | solution 1 for PCSPBLPAff.Symmetric.W_nonneg_sum
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:52:25.346657+00:00
-- url     : https://prove2.me/submissions/cdf02c47-7f1a-4241-a6d0-0536efd1e031

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

open PCSPBLPAff.Symmetric

theorem solution {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (X : Instance τ ar) (𝔸 : RelStruct τ ar A) (w : Fin X.n → A → ℚ)
    (p : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℚ) (r : Fin X.n → A → ℤ)
    (q : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℤ)
    (hLP : IsLPSol X 𝔸 w p) (hAff : IsAffSol X 𝔸 r q) (href : ∀ i a, w i a = 0 → r i a = 0)
    (ℓ : ℕ) (hℓ : 0 < ℓ) (hw : ∀ i a, ∃ z : ℤ, (ℓ : ℚ) * w i a = z)
    (M : ℕ) (hr : ∀ i a, |r i a| ≤ M)
    (u v L : ℕ) (hL : L = u * ℓ + v) (hv : v < ℓ) (hLM : M * ℓ ^ 2 ≤ L) :
    ∀ i, ∃ W : A → ℕ, (∀ a, (W a : ℚ) = u * ℓ * w i a + v * r i a) ∧ ∑ a, W a = L := by
  intro i
  choose z hz using hw
  have hMu : M * ℓ ≤ u := by
    by_contra h
    push_neg at h
    have h2 : (u + 1) * ℓ ≤ M * ℓ * ℓ := Nat.mul_le_mul_right ℓ h
    nlinarith
  have hMuZ : (M : ℤ) * ℓ ≤ u := by exact_mod_cast hMu
  have hnn : ∀ a, 0 ≤ (u : ℤ) * z i a + v * r i a := by
    intro a
    by_cases hw0 : w i a = 0
    · have hr0 := href i a hw0
      have hz0 : z i a = 0 := by
        have := hz i a
        rw [hw0, mul_zero] at this
        exact_mod_cast this.symm
      rw [hr0, hz0]; simp
    · have hwpos : 0 < w i a := lt_of_le_of_ne (hLP.1 i a) (Ne.symm hw0)
      have hzpos : (0 : ℚ) < z i a := by
        rw [← hz i a]; exact mul_pos (by exact_mod_cast hℓ) hwpos
      have hz1 : 1 ≤ z i a := by exact_mod_cast hzpos
      have hra : -(M : ℤ) ≤ r i a := neg_le_of_abs_le (hr i a)
      have hvl : (v : ℤ) ≤ ℓ := by exact_mod_cast hv.le
      have hu0 : (0 : ℤ) ≤ u := by positivity
      have hv0 : (0 : ℤ) ≤ v := by positivity
      have hM0 : (0 : ℤ) ≤ M := by positivity
      have e1 : (v : ℤ) * M ≤ ℓ * M := mul_le_mul_of_nonneg_right hvl hM0
      have e2 : (u : ℤ) ≤ u * z i a := le_mul_of_one_le_right hu0 hz1
      have e3 : (v : ℤ) * (-(M : ℤ)) ≤ v * r i a := mul_le_mul_of_nonneg_left hra hv0
      nlinarith
  refine ⟨fun a => ((u : ℤ) * z i a + v * r i a).toNat, ?_, ?_⟩
  · intro a
    have h1 : ((((u : ℤ) * z i a + v * r i a).toNat : ℤ) : ℚ) = (((u : ℤ) * z i a + v * r i a : ℤ) : ℚ) := by
      rw [Int.toNat_of_nonneg (hnn a)]
    have h2 : ((((u : ℤ) * z i a + v * r i a).toNat : ℕ) : ℚ) = ((((u : ℤ) * z i a + v * r i a).toNat : ℤ) : ℚ) := by
      norm_cast
    rw [h2, h1]
    push_cast
    rw [← hz i a]
    ring
  · have hsum : ∀ a, ((((u : ℤ) * z i a + v * r i a).toNat : ℕ) : ℚ) = u * ℓ * w i a + v * r i a := by
      intro a
      have h1 : ((((u : ℤ) * z i a + v * r i a).toNat : ℤ) : ℚ) = (((u : ℤ) * z i a + v * r i a : ℤ) : ℚ) := by
        rw [Int.toNat_of_nonneg (hnn a)]
      have h2 : ((((u : ℤ) * z i a + v * r i a).toNat : ℕ) : ℚ) = ((((u : ℤ) * z i a + v * r i a).toNat : ℤ) : ℚ) := by
        norm_cast
      rw [h2, h1]
      push_cast
      rw [← hz i a]
      ring
    apply Nat.cast_injective (R := ℚ)
    rw [Nat.cast_sum]
    simp only [hsum]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hLP.2.2.2.1 i]
    have hr1 : (∑ a, (r i a : ℚ)) = 1 := by
      rw [← Int.cast_sum, hAff.2.1 i]; simp
    rw [hr1, hL]
    push_cast
    ring
