-- Prove2me | solution 1 for TSTutorial.KnownStandard.stationary_deterministic_linear_regret
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:14:48.5929+00:00
-- url     : https://prove2.me/submissions/e3be776c-264a-4bc4-a7f6-e08099b766aa

import Theorems.Thm_TSTutorial_KnownStandard_case_first_action_one
import Theorems.Thm_TSTutorial_KnownStandard_case_first_action_two

open TSTutorial.KnownStandard


theorem solution (f : Strategy) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ ≤ 1 ∧
      ∃ c : ℝ, 0 < c ∧ ∀ T : ℕ, c * T ≤ expRegret f p₀ T := by
  classical
  by_cases h : ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ f p = 0
  · obtain ⟨p, hp, hp1, hf⟩ := h
    refine ⟨p, hp, hp1, p / 4, by positivity, ?_⟩
    intro T
    rw [(case_first_action_one f p hp hp1 hf T).2]
    exact le_of_eq (mul_comm _ _)
  · have hf : ∀ p : ℝ, 0 < p → p ≤ 1 → f p = 1 := by
      intro p hp hp1
      have hn : f p ≠ 0 := fun hz => h ⟨p, hp, hp1, hz⟩
      have hb := (f p).isLt
      apply Fin.ext
      have hv : (f p).val ≠ 0 := fun hz => hn (Fin.ext hz)
      change (f p).val = 1
      omega
    refine ⟨1 / 2, by norm_num, by norm_num, 1 / 8, by norm_num, ?_⟩
    intro T
    rw [(case_first_action_two f hf (1 / 2) (by norm_num) (by norm_num) T).2]
    exact le_of_eq (by ring)


