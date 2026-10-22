-- Prove2me | solution 1 for UtilityTokens.ICOChoice.reduced_ico_problem
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:58:19.154083+00:00
-- url     : https://prove2.me/submissions/0e7d8d69-6700-47e2-9c46-dae8de46c2de

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting
set_option autoImplicit false
open UtilityTokens.ICOChoice

theorem solution (Θ x f : ℝ) (hΘ1 : 1 < Θ) (hx : 0 < x) :
    let g : ℝ → ℝ := fun θbar =>
      (Θ - θbar) / Θ * x * ((Θ - θbar) / Θ * (θbar - 1) + 1) - f
    (∀ θbar ∈ Set.Icc 1 Θ,
      profitI Θ x f θbar (basicUtility Θ x θbar) = g θbar) ∧
    IsGreatest (g '' Set.Icc 1 Θ) (optPayoffI Θ x f) := by
  intro g
  have hΘ0 : 0 < Θ := by linarith
  have hprof : ∀ θ ∈ Set.Icc (1:ℝ) Θ, profitI Θ x f θ (basicUtility Θ x θ) = g θ := by
    intro θ _
    unfold profitI demandI1 demandI0 thresholdPrice
    rw [if_pos rfl]
    by_cases h : θ = 1
    · subst h
      simp only [g, if_true, basicUtility, activeShare]
      ring
    · simp only [g, if_neg h, basicUtility, activeShare]
      ring
  have hle : ∀ θ ∈ Set.Icc (1:ℝ) Θ, ∀ p1 : ℝ, profitI Θ x f θ p1 ≤ g θ := by
    intro θ hθ p1
    by_cases hp : p1 = basicUtility Θ x θ
    · subst hp; exact (hprof θ hθ).le
    · unfold profitI demandI1 demandI0 thresholdPrice
      rw [if_neg hp]
      by_cases h : θ = 1
      · subst h
        simp only [g, if_true, basicUtility, activeShare]
        apply le_of_eq; ring
      · simp only [g, if_neg h, basicUtility, activeShare]
        have ha0 : 0 ≤ (Θ - θ) / Θ := div_nonneg (by linarith [hθ.2]) hΘ0.le
        have ha1 : (Θ - θ) / Θ ≤ 1 := by
          rw [div_le_one hΘ0]; linarith [hθ.1]
        set a := (Θ - θ) / Θ with ha
        nlinarith [mul_nonneg (mul_nonneg ha0 hx.le) (sub_nonneg.2 ha1)]
  have hcont : ContinuousOn g (Set.Icc 1 Θ) := by
    have : Continuous g := by
      simp only [g]; fun_prop
    exact this.continuousOn
  obtain ⟨θ0, hθ0, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hΘ1.le) hcont
  have hv0 : 0 ≤ basicUtility Θ x θ0 := by
    unfold basicUtility activeShare
    exact mul_nonneg (div_nonneg (by linarith [hθ0.2]) hΘ0.le) hx.le
  have hS : IsGreatest ((fun c : ℝ × ℝ => profitI Θ x f c.1 c.2) '' ICOChoices Θ x) (g θ0) := by
    constructor
    · refine ⟨(θ0, basicUtility Θ x θ0), ⟨hθ0, le_refl _, by nlinarith⟩, ?_⟩
      exact hprof θ0 hθ0
    · rintro _ ⟨c, hc, rfl⟩
      exact (hle c.1 hc.1 c.2).trans (hmax (hc.1))
  have hopt : optPayoffI Θ x f = g θ0 := hS.csSup_eq
  refine ⟨hprof, ?_⟩
  rw [hopt]
  exact ⟨⟨θ0, hθ0, rfl⟩, by rintro _ ⟨t, ht, rfl⟩; exact hmax ht⟩
