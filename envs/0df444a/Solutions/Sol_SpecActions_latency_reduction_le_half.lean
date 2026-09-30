-- Prove2me | solution 1 for SpecActions.latency_reduction_le_half
-- status  : ACCEPTED   (prove)
-- author  : @naimengye
-- created : 2026-09-11T15:54:30.021634+00:00
-- url     : https://prove2.me/submissions/2d470f7b-ec69-4779-84cd-59d4481edf84

import Definitions.Def_SpecActions_model

open SpecActions

theorem solution (α β pk : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hpk0 : 0 ≤ pk) (hpk1 : pk ≤ 1) :
    pk / (1 + pk) * (α / (α + β)) < 1 / 2 := by
  have hp1 : (0:ℝ) < 1 + pk := by linarith
  have hab : (0:ℝ) < α + β := by linarith
  -- `pk/(1+pk) ≤ 1/2`, since `1/2 - pk/(1+pk) = (1-pk)/(2(1+pk)) ≥ 0`.
  have hAexp : (1:ℝ) / 2 - pk / (1 + pk) = (1 - pk) / (2 * (1 + pk)) := by
    field_simp; ring
  have hAnn : (0:ℝ) ≤ (1 - pk) / (2 * (1 + pk)) :=
    div_nonneg (by linarith) (by linarith)
  have hA : pk / (1 + pk) ≤ 1 / 2 := by linarith
  have hA0 : 0 ≤ pk / (1 + pk) := div_nonneg hpk0 (le_of_lt hp1)
  -- `α/(α+β) < 1` strictly, since `1 - α/(α+β) = β/(α+β) > 0`.
  have hBexp : (1:ℝ) - α / (α + β) = β / (α + β) := by
    field_simp; ring
  have hBpos : (0:ℝ) < β / (α + β) := div_pos hβ hab
  have hB : α / (α + β) < 1 := by linarith
  have hB0 : 0 < α / (α + β) := div_pos hα hab
  nlinarith
