-- Prove2me | solution 1 for WittenAdSHolography.hawking_page
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T15:46:15.351894+00:00
-- url     : https://prove2.me/submissions/026a16a6-ac7e-4c34-8638-3eb996ffe6ad

import Mathlib
import Definitions.Def_WittenAdSHolography_Defs

open WittenAdSHolography MeasureTheory Filter Topology in
theorem solution (β I : ℝ → ℝ)
    (hβ : ∀ r, β r = 12 * Real.pi * r / (1 + 3 * r ^ 2))
    (hI : ∀ r, I r = Real.pi * r ^ 2 * (1 - r ^ 2) / (1 + 3 * r ^ 2)) :
    (∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → β r ≤ β r₀) ∧
      ∃ R : ℝ, ∀ r : ℝ, R < r → I r < 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨⟨Real.sqrt 3 / 3, by positivity, ?_⟩, ⟨1, ?_⟩⟩
  · intro r _hr
    rw [hβ, hβ]
    have h1 : (0:ℝ) < 1 + 3 * r ^ 2 := by positivity
    have h2 : (0:ℝ) < 1 + 3 * (Real.sqrt 3 / 3) ^ 2 := by positivity
    rw [div_le_div_iff₀ h1 h2]
    have key : 0 ≤ 4 * Real.pi * Real.sqrt 3 * (Real.sqrt 3 * r - 1) ^ 2 := by positivity
    have e : 12 * Real.pi * (Real.sqrt 3 / 3) * (1 + 3 * r ^ 2)
        - 12 * Real.pi * r * (1 + 3 * (Real.sqrt 3 / 3) ^ 2)
        = 4 * Real.pi * Real.sqrt 3 * (Real.sqrt 3 * r - 1) ^ 2 := by
      linear_combination (4 * Real.pi * r - 4 * Real.pi * Real.sqrt 3 * r ^ 2) * hs3
    linarith [key, e]
  · intro r hr
    rw [hI]
    have h1 : (0:ℝ) < 1 + 3 * r ^ 2 := by positivity
    apply div_neg_of_neg_of_pos _ h1
    have hr2 : 1 < r ^ 2 := by nlinarith
    have : 0 < Real.pi * r ^ 2 := by positivity
    nlinarith
