-- Prove2me | solution 1 for WrightPDIPM.SelfDual.theorem_9_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:33:52.461699+00:00
-- url     : https://prove2.me/submissions/5d6dfe42-17c0-4e8e-963d-57e700ae83e0

import Mathlib
import Definitions.Def_WrightPDIPM_SelfDual_Setup
open WrightPDIPM.SelfDual

open Matrix

theorem g69b_sd94_key {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (lam0 : Fin m → ℝ) (s0 : Fin n → ℝ)
    (hx0 : ∀ j, 0 < x0 j) (hs0 : ∀ j, 0 < s0 j)
    (τ : ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (θ κ : ℝ) (s : Fin n → ℝ)
    (hsol : IsSolution98 A b c x0 lam0 s0 τ x lam θ κ s) :
    θ = 0 := by
  obtain ⟨hκ, hs, h0m, h0, hτ, hx, hκ0, hs', hc⟩ := hsol
  have e2 : A *ᵥ x = τ • b - θ • bbar A b x0 := by
    funext i
    have := congrFun h0m i
    simp only [Pi.zero_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have e1 : x ⬝ᵥ s = τ * (x ⬝ᵥ c) - (A *ᵥ x) ⬝ᵥ lam - θ * (x ⬝ᵥ cbar A c lam0 s0) := by
    rw [hs, dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_mulVec,
      vecMul_transpose]
    simp [smul_eq_mul]
  rw [e2, sub_dotProduct, smul_dotProduct, smul_dotProduct] at e1
  simp only [smul_eq_mul] at e1
  have hpos : 0 ≤ x0 ⬝ᵥ s0 := by
    unfold dotProduct
    exact Finset.sum_nonneg (fun j _ => (mul_pos (hx0 j) (hs0 j)).le)
  have key : θ * (x0 ⬝ᵥ s0 + 1) = 0 := by
    rw [dotProduct_comm x c, dotProduct_comm x (cbar A c lam0 s0)] at e1
    linear_combination hc - τ * hκ - e1 - θ * h0
  rcases mul_eq_zero.mp key with h | h
  · exact h
  · linarith

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
    (x0 : Fin n → ℝ) (lam0 : Fin m → ℝ) (s0 : Fin n → ℝ)
    (hx0 : ∀ j, 0 < x0 j) (hs0 : ∀ j, 0 < s0 j)
    (τ : ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (θ κ : ℝ) (s : Fin n → ℝ)
    (hsc : IsStrictlyComplementary98 A b c x0 lam0 s0 τ x lam θ κ s) (hκ : 0 < κ) :
    (c ⬝ᵥ x < 0 ∨ -(b ⬝ᵥ lam) < 0) ∧
    (c ⬝ᵥ x < 0 → ¬ ∃ (lam' : Fin m → ℝ) (s' : Fin n → ℝ), DualFeasible A c lam' s') ∧
    (-(b ⬝ᵥ lam) < 0 → ¬ ∃ x' : Fin n → ℝ, PrimalFeasible A b x') := by
  have hθ := g69b_sd94_key A b c x0 lam0 s0 hx0 hs0 τ x lam θ κ s hsc.1
  obtain ⟨⟨hκe, hs, h0m, _, hτ, hx, hκ0, hs0', hc⟩, _, _⟩ := hsc
  subst hθ
  have hd : 0 ≤ x ⬝ᵥ s := Finset.sum_nonneg (fun j _ => mul_nonneg (hx j) (hs0' j))
  have hτ0 := g69b_tau_zero τ κ _ hτ hκ hd hc
  subst hτ0
  have hAx : A *ᵥ x = 0 := by simpa using h0m.symm
  have hs' : s = -(Aᵀ *ᵥ lam) := by rw [hs]; simp
  have hκe' : κ = -(c ⬝ᵥ x) + b ⬝ᵥ lam := by rw [hκe]; simp
  exact g69b_sd_core A b c x lam κ s hAx hs' hκe' hκ hx hs0'
