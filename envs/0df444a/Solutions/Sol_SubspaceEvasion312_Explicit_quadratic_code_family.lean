-- Prove2me | solution 1 for SubspaceEvasion312.Explicit.quadratic_code_family
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:05:32.99419+00:00
-- url     : https://prove2.me/submissions/193182b0-125e-4ea4-ba8c-c84af3a11526
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SubspaceEvasion312_Explicit_effective
import Theorems.Thm_SubspaceEvasion312_Explicit_constant_alphabet_design
import Theorems.Thm_SubspaceEvasion312_Explicit_small_design_recovery

section
set_option autoImplicit false

namespace SubspaceEvasion312.Explicit
open scoped ENNReal

theorem chk_quadratic_code_family :
    ∃ A a h : ℕ, 0 < A ∧
    ∀ (F : Type) [Field F] [Fintype F] (r : ℕ), 0 < r →
    ∃ (s K m₀ : ℕ) (C : ∀ m, Code F s m) (k : ℕ → ℕ)
      (E : ∀ m, Vec F (k m) →ₗ[F] Blocks F s m)
      (τ : ℕ → ℕ → ℝ) (gen enc : Program F),
      0 < s ∧ 0 < K ∧ 0 < m₀ ∧
      (s : ℝ) ≤ A * (1 + (r : ℝ))^a * (Fintype.card F : ℝ)^(r^2) ∧
      CodeAlgorithms k E gen enc (fun m => K*(m+1)^h) (fun m => K*(m+1)^h) m₀ ∧
      ∀ m ≥ m₀, IsEncoder (C m) (E m) ∧ 1 / (2*(r : ℝ)) ≤ codeRate (C m) ∧
        SubspaceDesign (C m) (τ m) ∧ τ m r < 1 / (r : ℝ) ∧
        ∀ ℓ : ℕ, ListRecoverable (C m) r 0 ℓ ℓ := by
  obtain ⟨A0, a0, h0, hA0, H⟩ := constant_alphabet_design
  refine ⟨A0 * 5 ^ a0, a0, h0, by positivity, ?_⟩
  intro F _ _ r hr
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < r := by linarith
  have hε : (0 : ℝ) < 1 / (4 * r) := by positivity
  have hε1 : 1 / (4 * (r : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  obtain ⟨K, hK, H2⟩ := H F r (1 / (4 * r)) hε hε1
  have hR : (0 : ℝ) < 1 / (2 * (r : ℝ)) := by positivity
  have hRε : 1 / (2 * (r : ℝ)) + 1 / (4 * r) ≤ 1 := by
    have : 1 / (2 * (r : ℝ)) + 1 / (4 * r) = 3 / (4 * r) := by field_simp; ring
    rw [this, div_le_one (by positivity)]; linarith
  obtain ⟨s, m₀, C, k, E, τ, gen, enc, hs, hm0, hsb, halg, hall⟩ := H2 (1 / (2 * r)) hR hRε
  refine ⟨s, K, m₀, C, k, E, τ, gen, enc, hs, hK, hm0, ?_, halg, ?_⟩
  · have h1 : (1 : ℝ) + r + 1 / (1 / (4 * (r : ℝ))) ≤ 5 * (1 + r) := by
      rw [one_div_one_div]; linarith
    have h2 : ((1 : ℝ) + r + 1 / (1 / (4 * (r : ℝ)))) ^ a0 ≤ (5 * (1 + r)) ^ a0 :=
      pow_le_pow_left₀ (by positivity) h1 a0
    calc (s : ℝ) ≤ A0 * (1 + r + 1 / (1 / (4 * (r : ℝ)))) ^ a0 * (Fintype.card F : ℝ) ^ (r ^ 2) := hsb
      _ ≤ A0 * (5 * (1 + r)) ^ a0 * (Fintype.card F : ℝ) ^ (r ^ 2) := by gcongr
      _ = ((A0 * 5 ^ a0 : ℕ) : ℝ) * (1 + (r : ℝ)) ^ a0 * (Fintype.card F : ℝ) ^ (r ^ 2) := by
          push_cast; rw [mul_pow]; ring
  · intro m hm
    obtain ⟨he, hrate, hd, hτ⟩ := hall m hm
    have hτ' : τ m r < 1 / (r : ℝ) := by
      have : 1 / (2 * (r : ℝ)) + 1 / (4 * r) < 1 / r := by
        have e : 1 / (2 * (r : ℝ)) + 1 / (4 * r) = 3 / 4 * (1 / r) := by field_simp; ring
        rw [e]
        have : (0 : ℝ) < 1 / r := by positivity
        linarith
      linarith
    exact ⟨he, hrate, hd, hτ',
      fun ℓ => small_design_recovery (by omega) (C m) (τ m) hd (Or.inr hτ') ℓ⟩
end SubspaceEvasion312.Explicit
end

theorem solution : type_of% @SubspaceEvasion312.Explicit.chk_quadratic_code_family := @SubspaceEvasion312.Explicit.chk_quadratic_code_family
