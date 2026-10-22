-- Prove2me | solution 1 for WrightPDIPM.SelfDual.theorem_9_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:31:29.513993+00:00
-- url     : https://prove2.me/submissions/afd8b57e-cb47-430f-be5e-ab9190aefe59

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

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (lam0 : Fin m → ℝ) (s0 : Fin n → ℝ)
    (hx0 : ∀ j, 0 < x0 j) (hs0 : ∀ j, 0 < s0 j)
    (τ : ℝ) (x : Fin n → ℝ) (lam : Fin m → ℝ) (θ κ : ℝ) (s : Fin n → ℝ)
    (hsol : IsSolution98 A b c x0 lam0 s0 τ x lam θ κ s) :
    θ = 0 :=
  g69b_sd94_key A b c x0 lam0 s0 hx0 hs0 τ x lam θ κ s hsol
