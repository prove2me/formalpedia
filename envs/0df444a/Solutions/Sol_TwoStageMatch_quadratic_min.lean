-- Prove2me | solution 1 for TwoStageMatch.quadratic_min
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:30:43.017319+00:00
-- url     : https://prove2.me/submissions/08e03ba7-39ef-420f-bf8c-641a8cb6be61

import Mathlib

theorem solution :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, (3 / 4 : ℝ) ≤ 1 - x + x ^ 2) ∧
    ((1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧ (1 : ℝ) - 1 / 2 + (1 / 2) ^ 2 = 3 / 4) := by
  refine ⟨fun x _ => by nlinarith [sq_nonneg (x - 1 / 2)], ⟨by norm_num, by norm_num⟩, by norm_num⟩
