-- Prove2me | solution 1 for UnfairML.Coverage.Supplement.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:23:00.025683+00:00
-- url     : https://prove2.me/submissions/4a3940c9-07e4-48e2-83d7-f0d0e342346f

import Mathlib
import Definitions.Def_UnfairML_Coverage_Supplement_GeneralFairness

open UnfairML
open UnfairML.Coverage
open UnfairML.Coverage.Supplement

/-- Theorem 4, p. 26: all global maximizing efforts are ordered at strictly
ordered fairness parameters; identical parameters use the same chosen optimizer. -/
theorem solution (P : Params) (hS : P.Standing) (τ : ℝ → ℝ)
    (hτ : IsLearningCost P τ) (θ₁ θ₂ : ℝ)
    (hθ₁ : 1 ≤ θ₁) (hθ : θ₁ < θ₂)
    (s₁ s₂ : ℝ) (h₁ : IsOptGeneral P τ θ₁ s₁) (h₂ : IsOptGeneral P τ θ₂ s₂) :
    s₂ ≤ s₁ := by
      obtain ⟨hα, hβ, hdr, hdrp, hdp, hab, hgp, hgr⟩ := hS
      obtain ⟨⟨⟨h1a, h1b⟩, h1c, h1d⟩, hopt1⟩ := h₁
      obtain ⟨⟨⟨h2a, h2b⟩, h2c, h2d⟩, hopt2⟩ := h₂
      by_contra hcon
      have hlt : s₁ < s₂ := not_le.mp hcon
      have hgr0 : 0 < P.γr := lt_trans hgp hgr
      have hD : 0 < P.βp - P.αp := by
        unfold Params.αr Params.βr at hab
        unfold Params.αp Params.βp
        have e1 : P.β * P.dr < P.β * P.dp := mul_lt_mul_of_pos_left hdrp hβ
        have e2 : P.α * (1 - P.dp) < P.α * (1 - P.dr) :=
          mul_lt_mul_of_pos_left (by linarith) hα
        linarith
      have hθ0 : 0 ≤ θ₂ - θ₁ := by linarith
      have hk : 0 < θ₂ * P.γr - P.γp := by nlinarith
      have hk1 : 0 < θ₁ * P.γr - P.γp := by nlinarith
      have f1 : GeneralFeasible P θ₁ s₂ := by
        refine ⟨⟨h2a, h2b⟩, ?_, ?_⟩
        · have : 0 ≤ (θ₂ - θ₁) * P.γr * s₂ := by positivity
          nlinarith
        · have : 0 ≤ (θ₁ * P.γr - P.γp) * s₂ := by positivity
          nlinarith
      have f2 : GeneralFeasible P θ₂ s₁ := by
        refine ⟨⟨h1a, h1b⟩, ?_, ?_⟩
        · have : 0 ≤ (θ₂ * P.γr + P.γp) * (s₂ - s₁) :=
            mul_nonneg (by nlinarith) (by linarith)
          nlinarith
        · have : 0 ≤ (θ₂ * P.γr - P.γp) * s₁ := by positivity
          nlinarith
      have g1 := hopt1 s₂ f1
      have g2 := hopt2 s₁ f2
      have hs2 : P.γr * s₂ ≤ 1 / 2 := by
        unfold Params.sMax at h2b
        rw [le_div_iff₀ (by positivity)] at h2b
        linarith
      have hp2 : 0 < 1 - P.γp * s₂ := by nlinarith
      have hp1 : 0 < 1 - P.γp * s₁ := by nlinarith
      have hfrac : s₁ / (1 - P.γp * s₁) < s₂ / (1 - P.γp * s₂) := by
        rw [div_lt_div_iff₀ hp1 hp2]
        nlinarith
      have key : ∀ s : ℝ, generalProfit P τ θ₂ s = generalProfit P τ θ₁ s
          - ((θ₂ - θ₁) * P.γr * (P.βp - P.αp)) * (s / (1 - P.γp * s)) := by
        intro s
        unfold generalProfit G1
        ring
      rw [key s₁, key s₂] at g2
      have hc : 0 < (θ₂ - θ₁) * P.γr * (P.βp - P.αp) :=
        mul_pos (mul_pos (by linarith) hgr0) hD
      have := mul_lt_mul_of_pos_left hfrac hc
      linarith
