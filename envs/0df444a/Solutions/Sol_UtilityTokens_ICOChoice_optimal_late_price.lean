-- Prove2me | solution 1 for UtilityTokens.ICOChoice.optimal_late_price
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:38:57.620987+00:00
-- url     : https://prove2.me/submissions/906fb664-5f25-4717-b43e-8112254241b2

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting

open UtilityTokens.ICOChoice in
theorem solution (Θ x f : ℝ) (hΘ1 : 1 < Θ) (hx : 0 < x) :
    ∀ θbar ∈ Set.Icc 1 Θ,
      ∀ p1 ∈ Set.Icc (basicUtility Θ x θbar) (Θ * basicUtility Θ x θbar),
        profitI Θ x f θbar p1 ≤ profitI Θ x f θbar (basicUtility Θ x θbar) := by
  intro θ hθ p1 _
  unfold profitI
  by_cases h : p1 = basicUtility Θ x θ
  · subst h
    exact le_rfl
  · have hu : 0 ≤ basicUtility Θ x θ := by
      unfold basicUtility activeShare
      exact mul_nonneg (div_nonneg (by linarith [hθ.2]) (by linarith)) hx.le
    have hD : demandI0 Θ θ ≤ 1 := by
      unfold demandI0 activeShare
      split_ifs with h0
      · exact le_rfl
      · rw [div_le_one (by linarith)]
        linarith [hθ.1]
    have h1 : demandI1 Θ x θ p1 = 0 := by
      unfold demandI1
      rw [if_neg h]
    have h2 : demandI1 Θ x θ (basicUtility Θ x θ) = 1 - demandI0 Θ θ := by
      unfold demandI1
      rw [if_pos rfl]
    rw [h1, h2]
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hD)]
