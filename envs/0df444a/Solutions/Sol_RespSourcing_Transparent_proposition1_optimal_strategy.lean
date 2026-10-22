-- Prove2me | solution 1 for RespSourcing.Transparent.proposition1_optimal_strategy
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:25:39.606742+00:00
-- url     : https://prove2.me/submissions/e1af0685-55c4-4fb5-9180-86d5592e1755

import Mathlib
import Definitions.Def_RespSourcing_Transparent_Model

set_option autoImplicit false
open RespSourcing.Transparent

theorem solution (p : Params) (hp : p.Standing) :
    (p.r < p.Δ →
      p.φ * (p.α * p.θ * (p.v - p.cNR) + p.cVP) <
        p.Δ - max (p.θ * p.r - (1 - p.θ) * (p.v - p.cR)) 0 →
      IsOptimal p .LC) ∧
    (p.Δ < p.r →
      p.φ * (p.α * p.θ * (p.v + p.r - p.cNR) + p.cVP) <
        p.Δ * (1 - p.θ) + p.θ * p.r -
          max (p.θ * p.r - (1 - p.θ) * (p.v - p.cR)) 0 →
      IsOptimal p .DS) ∧
    (0 < p.θ →
      (p.v - p.cR) * (1 - p.θ) / p.θ < p.r →
      ¬ IsOptimal p .LC → ¬ IsOptimal p .DS → IsOptimal p .RN) ∧
    (0 < p.θ →
      p.r < (p.v - p.cR) * (1 - p.θ) / p.θ →
      ¬ IsOptimal p .LC → ¬ IsOptimal p .DS → IsOptimal p .RM) := by
  obtain ⟨hθ0, hθ1, hα0, hα1, hφ0, hφ1, hc⟩ := hp
  have hΔ : p.Δ = p.cR - p.cNR := rfl
  have hΔpos : 0 < p.Δ := by rw [hΔ]; linarith
  have hαφ : 0 ≤ 1 - p.α * p.φ := by nlinarith [mul_nonneg hα0 hφ0, mul_le_mul hα1 hφ1 hφ0 zero_le_one]
  have hcoef : 0 ≤ (1 - p.α * p.φ) * p.θ := mul_nonneg hαφ hθ0
  have hDSLC : profit p .DS - profit p .LC = ((1 - p.α * p.φ) * p.θ) * (p.r - p.Δ) := by
    simp only [profit, Params.Δ]; ring
  have hm1 : p.θ * p.r - (1 - p.θ) * (p.v - p.cR) ≤
      max (p.θ * p.r - (1 - p.θ) * (p.v - p.cR)) 0 := le_max_left _ _
  have hm2 : (0 : ℝ) ≤ max (p.θ * p.r - (1 - p.θ) * (p.v - p.cR)) 0 := le_max_right _ _
  have hq : 0 ≤ p.φ * p.α * p.θ * p.Δ :=
    mul_nonneg (mul_nonneg (mul_nonneg hφ0 hα0) hθ0) hΔpos.le
  have hex : ∃ m : Strategy, ∀ t, profit p t ≤ profit p m := by
    obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ (profit p)
      (⟨.LC, Finset.mem_univ _⟩ : (Finset.univ : Finset Strategy).Nonempty)
    exact ⟨m, fun t => hm t (Finset.mem_univ t)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hr h t
    have h1 : 0 ≤ ((1 - p.α * p.φ) * p.θ) * (p.Δ - p.r) := mul_nonneg hcoef (by linarith)
    cases t
    · exact le_refl _
    · simp only [profit, Params.Δ] at h1 ⊢
      nlinarith [h1]
    · simp only [profit, Params.Δ] at h hm1 hm2 ⊢
      nlinarith [h, hm1]
    · simp only [profit, Params.Δ] at h hm1 hm2 ⊢
      nlinarith [h, hm2]
  · intro hr h t
    have h1 : 0 ≤ ((1 - p.α * p.φ) * p.θ) * (p.r - p.Δ) := mul_nonneg hcoef (by linarith)
    cases t
    · simp only [profit, Params.Δ] at h1 ⊢
      nlinarith [h1]
    · exact le_refl _
    · simp only [profit, Params.Δ] at h hm1 hm2 hq ⊢
      nlinarith [h, hm1, hq]
    · simp only [profit, Params.Δ] at h hm1 hm2 hq ⊢
      nlinarith [h, hm2, hq]
  · intro hθ hr hLC hDS
    have h1 : (p.v - p.cR) * (1 - p.θ) < p.r * p.θ := (div_lt_iff₀ hθ).1 hr
    obtain ⟨m, hm⟩ := hex
    cases m
    · exact absurd hm hLC
    · exact absurd hm hDS
    · exact hm
    · have := hm .RN
      simp only [profit] at this
      nlinarith [h1]
  · intro hθ hr hLC hDS
    have h1 : p.r * p.θ < (p.v - p.cR) * (1 - p.θ) := (lt_div_iff₀ hθ).1 hr
    obtain ⟨m, hm⟩ := hex
    cases m
    · exact absurd hm hLC
    · exact absurd hm hDS
    · have := hm .RM
      simp only [profit] at this
      nlinarith [h1]
    · exact hm
