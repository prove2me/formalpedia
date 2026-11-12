-- Prove2me | solution 1 for SubspaceEvasion312.Explicit.logarithmic_code_family
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:05:32.963533+00:00
-- url     : https://prove2.me/submissions/56c93c5d-4d94-4346-8999-e4776f833b6c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SubspaceEvasion312_Explicit_effective
import Theorems.Thm_SubspaceEvasion312_Explicit_constant_alphabet_design
import Theorems.Thm_SubspaceEvasion312_Explicit_zero_error_recovery

section
set_option autoImplicit false

namespace SubspaceEvasion312.Explicit
open scoped ENNReal

theorem chk_logarithmic_code_family :
    ∃ A a h : ℕ, 0 < A ∧
    ∀ (F : Type) [Field F] [Fintype F] (r ℓ : ℕ), 0 < ℓ →
    ∃ (s K m₀ : ℕ) (C : ∀ m, Code F s m) (k : ℕ → ℕ)
      (E : ∀ m, Vec F (k m) →ₗ[F] Blocks F s m)
      (τ : ℕ → ℕ → ℝ) (gen enc : Program F),
      0 < s ∧ 0 < K ∧ 0 < m₀ ∧
      (s : ℝ) ≤ A * (1 + r + log₂ (ℓ : ℝ))^a * (Fintype.card F : ℝ)^(r^2) ∧
      CodeAlgorithms k E gen enc (fun m => K*(m+1)^h) (fun m => K*(m+1)^h) m₀ ∧
      ∀ m ≥ m₀, IsEncoder (C m) (E m) ∧
        1 / (2 + 2 * log₂ (ℓ : ℝ)) ≤ codeRate (C m) ∧
        SubspaceDesign (C m) (τ m) ∧ τ m r ≤ 1 / (1 + log₂ (ℓ : ℝ)) ∧
        ListRecoverable (C m) r 0 ℓ (2*ℓ) := by
  obtain ⟨A0, a0, h0, hA0, H⟩ := constant_alphabet_design
  refine ⟨A0 * 3 ^ a0, a0, h0, by positivity, ?_⟩
  intro F _ _ r ℓ hℓ
  have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hL : 0 ≤ log₂ (ℓ : ℝ) := by
    unfold log₂
    exact div_nonneg (Real.log_nonneg hℓR) (Real.log_nonneg (by norm_num))
  set L := log₂ (ℓ : ℝ) with hLdef
  have hD : (0 : ℝ) < 2 + 2 * L := by linarith
  have hε : (0 : ℝ) < 1 / (2 + 2 * L) := by positivity
  have hε1 : 1 / (2 + 2 * L) ≤ 1 := by
    rw [div_le_one hD]; linarith
  obtain ⟨K, hK, H2⟩ := H F r (1 / (2 + 2 * L)) hε hε1
  have hsum : 1 / (2 + 2 * L) + 1 / (2 + 2 * L) = 1 / (1 + L) := by
    field_simp; ring
  have hRε : 1 / (2 + 2 * L) + 1 / (2 + 2 * L) ≤ 1 := by
    rw [hsum, div_le_one (by linarith)]; linarith
  obtain ⟨s, m₀, C, k, E, τ, gen, enc, hs, hm0, hsb, halg, hall⟩ := H2 (1 / (2 + 2 * L)) hε hRε
  refine ⟨s, K, m₀, C, k, E, τ, gen, enc, hs, hK, hm0, ?_, halg, ?_⟩
  · have h1 : (1 : ℝ) + r + 1 / (1 / (2 + 2 * L)) ≤ 3 * (1 + r + L) := by
      rw [one_div_one_div]; have : (0 : ℝ) ≤ r := by positivity
      linarith
    have h2 : ((1 : ℝ) + r + 1 / (1 / (2 + 2 * L))) ^ a0 ≤ (3 * (1 + r + L)) ^ a0 :=
      pow_le_pow_left₀ (by have : (0 : ℝ) ≤ r := by positivity
                           rw [one_div_one_div]; linarith) h1 a0
    calc (s : ℝ) ≤ A0 * (1 + r + 1 / (1 / (2 + 2 * L))) ^ a0 * (Fintype.card F : ℝ) ^ (r ^ 2) := hsb
      _ ≤ A0 * (3 * (1 + r + L)) ^ a0 * (Fintype.card F : ℝ) ^ (r ^ 2) := by gcongr
      _ = ((A0 * 3 ^ a0 : ℕ) : ℝ) * (1 + (r : ℝ) + L) ^ a0 * (Fintype.card F : ℝ) ^ (r ^ 2) := by
          push_cast; rw [mul_pow]; ring
  · intro m hm
    obtain ⟨he, hrate, hd, hτ⟩ := hall m hm
    have hτ' : τ m r ≤ 1 / (1 + L) := by rw [← hsum]; exact hτ
    exact ⟨he, hrate, hd, hτ',
      ((zero_error_recovery (by omega) (C m) (τ m) hd ℓ).2.2 hℓ hτ')⟩
end SubspaceEvasion312.Explicit
end

theorem solution : type_of% @SubspaceEvasion312.Explicit.chk_logarithmic_code_family := @SubspaceEvasion312.Explicit.chk_logarithmic_code_family
