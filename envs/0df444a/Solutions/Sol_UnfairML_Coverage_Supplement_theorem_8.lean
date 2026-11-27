-- Prove2me | solution 1 for UnfairML.Coverage.Supplement.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:23:27.81966+00:00
-- url     : https://prove2.me/submissions/7dd91da1-cd25-499e-8deb-2c6743c42b8c

import Mathlib
import Definitions.Def_UnfairML_Coverage_Supplement_Response

open UnfairML
open UnfairML.Coverage
open UnfairML.Coverage.Supplement

/-- Theorem 8, p. 39: compare globally optimal efforts at distinct protected
default rates with all fixed data and the same arbitrary convex increasing cost. -/
theorem solution (β dr c γp γr : ℝ) (hc : 0 < c) (τ : ℝ → ℝ)
    (u₁ u₂ : ℝ) (hu : u₁ < u₂)
    (hS₁ : (responseParams β dr c γp γr u₁).Standing)
    (hS₂ : (responseParams β dr c γp γr u₂).Standing)
    (hL₁ : (responseParams β dr c γp γr u₁).LowLoss)
    (hL₂ : (responseParams β dr c γp γr u₂).LowLoss)
    (hτ : IsLearningCost (responseParams β dr c γp γr u₁) τ)
    (s₁ s₂ : ℝ)
    (h₁ : IsOptResponse β dr c γp γr τ u₁ s₁)
    (h₂ : IsOptResponse β dr c γp γr τ u₂ s₂) :
    s₁ ≤ s₂ := by
      obtain ⟨ha1, hb, hdr, hd1, hu1, -, hgp, hgr⟩ := hS₁
      obtain ⟨ha2, -, -, hd2, hu2, -, -, -⟩ := hS₂
      obtain ⟨hm1, ho1⟩ := h₁
      obtain ⟨hm2, ho2⟩ := h₂
      have e1 := ho1 s₂ hm2
      have e2 := ho2 s₁ hm1
      simp only [responseParams, Params.sMax, responseProfit, Params.αr, Params.αp, Params.βp]
        at ha1 hb hdr hd1 hu1 hgp hgr ha2 hd2 hu2 hm1 hm2 e1 e2
      by_contra hcon
      push Not at hcon
      have hx1 : 0 < 2 - u₁ - dr := by linarith
      have hx2 : 0 < 2 - u₂ - dr := by linarith
      have hr0 : 0 < γr := by linarith
      have m1 : responseAlpha β dr c u₁ * (2 - u₁ - dr) = β * (u₁ + dr) - 2 * c := by
        unfold responseAlpha; field_simp
      have m2 : responseAlpha β dr c u₂ * (2 - u₂ - dr) = β * (u₂ + dr) - 2 * c := by
        unfold responseAlpha; field_simp
      generalize responseAlpha β dr c u₁ = a1 at *
      generalize responseAlpha β dr c u₂ = a2 at *
      have hA : a1 ≤ a2 := by
        have : (a2 - a1) * (2 - u₂ - dr) = (a1 + β) * (u₂ - u₁) := by linarith
        have h3 : 0 < (a2 - a1) * (2 - u₂ - dr) := by
          rw [this]; exact mul_pos (by linarith) (by linarith)
        have := (pos_iff_pos_of_mul_pos h3).2 hx2
        linarith
      obtain ⟨h10, h11⟩ := hm1
      obtain ⟨h20, h21⟩ := hm2
      have k1 : γr * s₁ ≤ 1 / 2 := by
        have := mul_le_mul_of_nonneg_left h11 hr0.le
        have h4 : γr * (1 / (2 * γr)) = 1 / 2 := by field_simp
        linarith
      have hs1 : 0 < s₁ := by linarith
      have k2 : γr * s₂ ≤ γr * s₁ := mul_le_mul_of_nonneg_left hcon.le hr0.le
      have l1 : γp * s₁ ≤ γr * s₁ := mul_le_mul_of_nonneg_right hgr.le h10
      have l2 : γp * s₂ ≤ γr * s₂ := mul_le_mul_of_nonneg_right hgr.le h20
      have p1 : 0 < 1 - γr * s₁ := by linarith
      have p2 : 0 < 1 - γr * s₂ := by linarith
      have q1 : 0 < 1 - γp * s₁ := by linarith
      have q2 : 0 < 1 - γp * s₂ := by linarith
      have d1 : s₁ / (1 - γr * s₁) - s₂ / (1 - γr * s₂)
          = (s₁ - s₂) * (1 / ((1 - γr * s₁) * (1 - γr * s₂))) := by
        rw [div_sub_div _ _ p1.ne' p2.ne', mul_one_div]; congr 1; ring
      have d2 : s₁ / (1 - γp * s₁) - s₂ / (1 - γp * s₂)
          = (s₁ - s₂) * (1 / ((1 - γp * s₁) * (1 - γp * s₂))) := by
        rw [div_sub_div _ _ q1.ne' q2.ne', mul_one_div]; congr 1; ring
      have d3 : 1 / ((1 - γp * s₁) * (1 - γp * s₂)) ≤ 1 / ((1 - γr * s₁) * (1 - γr * s₂)) := by
        apply one_div_le_one_div_of_le (mul_pos p1 p2)
        exact mul_le_mul (by linarith) (by linarith) p2.le q1.le
      have d4 : 0 < s₁ / (1 - γp * s₁) - s₂ / (1 - γp * s₂) := by
        rw [d2]
        exact mul_pos (by linarith) (by positivity)
      have d5 : s₁ / (1 - γp * s₁) - s₂ / (1 - γp * s₂)
          ≤ s₁ / (1 - γr * s₁) - s₂ / (1 - γr * s₂) := by
        rw [d1, d2]
        exact mul_le_mul_of_nonneg_left d3 (by linarith)
      simp only [mul_div_assoc] at e1 e2
      generalize s₁ / (1 - γr * s₁) = G1 at *
      generalize s₂ / (1 - γr * s₂) = G2 at *
      generalize s₁ / (1 - γp * s₁) = H1 at *
      generalize s₂ / (1 - γp * s₂) = H2 at *
      have f1 : 0 ≤ ((a2 - a1) * (1 - dr) * γr) * ((G1 - G2) - (H1 - H2)) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hr0.le) (by linarith)
      have f2 : 0 < (β * γp * (u₂ - u₁)) * (H1 - H2) :=
        mul_pos (mul_pos (mul_pos hb hgp) (by linarith)) d4
      have f3 : (a2 * (1 - u₂) - β * u₂) - (a1 * (1 - u₁) - β * u₁) = -((a2 - a1) * (1 - dr)) := by
        linarith
      have f4 := congrArg (fun z => z * (γr * (H1 - H2))) f3
      linarith
