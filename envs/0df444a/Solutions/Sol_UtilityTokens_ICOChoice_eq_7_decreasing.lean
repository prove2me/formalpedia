-- Prove2me | solution 1 for UtilityTokens.ICOChoice.eq_7_decreasing
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:34:28.506309+00:00
-- url     : https://prove2.me/submissions/96efab5a-d527-4c76-889d-9a1ea4bb9f8a

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting
set_option autoImplicit false
open UtilityTokens.ICOChoice

theorem solution (Θ x : ℝ) (hΘ1 : 1 < Θ) (hΘ3 : Θ ≤ 3) (hx : 0 < x) :
    (∀ θbar ∈ Set.Ioc 1 Θ, profitT Θ x θbar = θbar * ((Θ - θbar) / Θ) ^ 2 * x) ∧
    StrictAntiOn (profitT Θ x) (Set.Ioc 1 Θ) ∧
    ∀ θbar ∈ Set.Ioc 1 Θ, profitT Θ x θbar < profitT Θ x 1 := by
  have hΘ0 : 0 < Θ := by linarith
  have h1 : ∀ θ ∈ Set.Ioc (1:ℝ) Θ, profitT Θ x θ = θ * ((Θ - θ) / Θ) ^ 2 * x := by
    intro θ hθ
    have hne : θ ≠ 1 := ne_of_gt hθ.1
    simp only [profitT, thresholdPrice, basicUtility, activeShare, demandT, if_neg hne]
    ring
  refine ⟨h1, ?_, ?_⟩
  · intro a ha b hb hab
    rw [h1 a ha, h1 b hb]
    obtain ⟨ha1, haΘ⟩ := ha
    obtain ⟨hb1, hbΘ⟩ := hb
    have hu : 0 < a - 1 := by linarith
    have hv : 0 < b - a := by linarith
    have hw : 0 ≤ Θ - b := by linarith
    have hw2 : 0 ≤ 2 - (Θ - b) := by linarith
    have hB : 0 < (b - a) * (a - 1) + 2 * (a - 1) * (Θ - b) + (b - a) + (Θ - b) * (2 - (Θ - b)) := by
      have := mul_pos hv hu
      have := mul_nonneg hu.le hw
      have := mul_nonneg hw hw2
      nlinarith
    have key : a * ((Θ - a) / Θ) ^ 2 * x - b * ((Θ - b) / Θ) ^ 2 * x
        = x * (b - a) * ((b - a) * (a - 1) + 2 * (a - 1) * (Θ - b) + (b - a)
            + (Θ - b) * (2 - (Θ - b))) / Θ ^ 2 := by
      field_simp
      ring
    have : 0 < x * (b - a) * ((b - a) * (a - 1) + 2 * (a - 1) * (Θ - b) + (b - a)
            + (Θ - b) * (2 - (Θ - b))) / Θ ^ 2 := by positivity
    linarith
  · intro θ hθ
    rw [h1 θ hθ]
    obtain ⟨hθ1, hθΘ⟩ := hθ
    have h1' : profitT Θ x 1 = (Θ - 1) / Θ * x := by
      simp [profitT, thresholdPrice, basicUtility, activeShare, demandT]
    rw [h1']
    have hu : 0 < θ - 1 := by linarith
    have hw : 0 ≤ Θ - θ := by linarith
    have hw2 : 0 ≤ 2 - (Θ - θ) := by linarith
    have hD : 0 < (θ - 1) ^ 2 + (θ - 1) + (Θ - θ) + (θ - 1) * (Θ - θ) * (2 - (Θ - θ)) := by
      have := mul_nonneg (mul_nonneg hu.le hw) hw2
      nlinarith [sq_nonneg (θ - 1)]
    have key : (Θ - 1) / Θ * x - θ * ((Θ - θ) / Θ) ^ 2 * x
        = x * ((θ - 1) ^ 2 + (θ - 1) + (Θ - θ) + (θ - 1) * (Θ - θ) * (2 - (Θ - θ))) / Θ ^ 2 := by
      field_simp
      ring
    have : 0 < x * ((θ - 1) ^ 2 + (θ - 1) + (Θ - θ) + (θ - 1) * (Θ - θ) * (2 - (Θ - θ))) / Θ ^ 2 := by
      positivity
    linarith
