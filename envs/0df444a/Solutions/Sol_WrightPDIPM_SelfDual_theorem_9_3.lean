-- Prove2me | solution 1 for WrightPDIPM.SelfDual.theorem_9_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:33:31.823884+00:00
-- url     : https://prove2.me/submissions/88378c37-b36b-48f2-ae47-919b91da6743

import Mathlib
import Definitions.Def_WrightPDIPM_SelfDual_Setup
open WrightPDIPM.SelfDual

open Matrix


theorem g69b_sd_core {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (κ : ℝ) (s : Fin n → ℝ)
    (hAx : A *ᵥ x = 0) (hs : s = -(Aᵀ *ᵥ lam)) (hκ : κ = -(c ⬝ᵥ x) + b ⬝ᵥ lam) (hκ0 : 0 < κ)
    (hx : ∀ j, 0 ≤ x j) (hs0 : ∀ j, 0 ≤ s j) :
    (c ⬝ᵥ x < 0 ∨ -(b ⬝ᵥ lam) < 0) ∧
    (c ⬝ᵥ x < 0 → ¬ ∃ (lam' : Fin m → ℝ) (s' : Fin n → ℝ), DualFeasible A c lam' s') ∧
    (-(b ⬝ᵥ lam) < 0 → ¬ ∃ x' : Fin n → ℝ, PrimalFeasible A b x') := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    push_neg at h
    linarith [h.1, h.2]
  · rintro hcx ⟨lam', s', hd1, hd2⟩
    have e : c ⬝ᵥ x = s' ⬝ᵥ x := by
      rw [← hd1, add_dotProduct, dotProduct_comm (Aᵀ *ᵥ lam') x, dotProduct_mulVec,
        vecMul_transpose, hAx]
      simp
    have : 0 ≤ s' ⬝ᵥ x := Finset.sum_nonneg (fun j _ => mul_nonneg (hd2 j) (hx j))
    linarith
  · rintro hbl ⟨x', hp1, hp2⟩
    have e : b ⬝ᵥ lam = -(x' ⬝ᵥ s) := by
      rw [← hp1, hs, dotProduct_neg, neg_neg, dotProduct_mulVec, vecMul_transpose]
    have : 0 ≤ x' ⬝ᵥ s := Finset.sum_nonneg (fun j _ => mul_nonneg (hp2 j) (hs0 j))
    linarith

theorem g69b_tau_zero (τ κ d : ℝ) (hτ : 0 ≤ τ) (hκ : 0 < κ) (hd : 0 ≤ d)
    (h : τ * κ + d = 0) : τ = 0 := by
  have : τ * κ = 0 := by nlinarith [mul_nonneg hτ hκ.le]
  rcases mul_eq_zero.mp this with h' | h'
  · exact h'
  · linarith

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (τ : ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (κ : ℝ) (s : Fin n → ℝ)
    (hsc : IsStrictlyComplementary95 A b c τ x lam κ s) (hκ : 0 < κ) :
    (c ⬝ᵥ x < 0 ∨ -(b ⬝ᵥ lam) < 0) ∧
    (c ⬝ᵥ x < 0 → ¬ ∃ (lam' : Fin m → ℝ) (s' : Fin n → ℝ), DualFeasible A c lam' s') ∧
    (-(b ⬝ᵥ lam) < 0 → ¬ ∃ x' : Fin n → ℝ, PrimalFeasible A b x') := by
  obtain ⟨⟨hκe, hs, h0m, hτ, hx, hκ0, hs0, hc⟩, _, _⟩ := hsc
  have hd : 0 ≤ x ⬝ᵥ s := Finset.sum_nonneg (fun j _ => mul_nonneg (hx j) (hs0 j))
  have hτ0 := g69b_tau_zero τ κ _ hτ hκ hd hc
  subst hτ0
  have hAx : A *ᵥ x = 0 := by simpa using h0m.symm
  have hs' : s = -(Aᵀ *ᵥ lam) := by rw [hs]; simp
  exact g69b_sd_core A b c x lam κ s hAx hs' hκe hκ hx hs0
