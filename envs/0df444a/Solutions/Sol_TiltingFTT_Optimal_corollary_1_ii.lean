-- Prove2me | solution 1 for TiltingFTT.Optimal.corollary_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:46:19.616205+00:00
-- url     : https://prove2.me/submissions/4df9d05c-aad0-446a-a49c-5fa56d8e3bb8

import Mathlib
import Definitions.Def_TiltingFTT_Optimal_Model

open TiltingFTT.Optimal

theorem solution (P : Firm) (hS : Standing P) :
    ∃ τ₀ : ℝ, 0 ≤ τ₀ ∧ ∀ τ, τ₀ ≤ τ → ∀ TP, ¬ IsPoolingEq P τ TP := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS
  have hFb : 0 < Fbar P := by
    unfold Fbar; nlinarith [mul_pos h11 (sub_pos.2 h8)]
  have hFbL : P.FbL < Fbar P := by
    unfold Fbar; nlinarith [mul_pos h11 (sub_pos.2 h8)]
  have hδI : 0 < P.δI := by linarith
  -- τ₀ = τ_FB: there (1+τ)δ_U ≥ δ_I, so (1+τ)δ_U F̄ > δ_I F̄_L
  refine ⟨P.δI / P.δU - 1, ?_, ?_⟩
  · have : 1 ≤ P.δI / P.δU := by rw [le_div_iff₀ h10]; linarith
    linarith
  · intro τ hτ TP hTP
    have hk : P.δI ≤ (1 + τ) * P.δU := by
      have : P.δI / P.δU ≤ 1 + τ := by linarith
      rwa [div_le_iff₀ h10] at this
    have hp : 0 ≤ (-(1 + τ) * P.δU * Fbar P + P.δI * P.FbL) :=
      (mul_nonneg_iff_of_pos_right hTP.1.1).1 hTP.2.2.1
    have := mul_le_mul_of_nonneg_right hk hFb.le
    have := mul_lt_mul_of_pos_left hFbL hδI
    linarith
