-- Prove2me | solution 1 for PolarizedLearning.expectedPosterior_informative
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:12:30.104918+00:00
-- url     : https://prove2.me/submissions/5a3f97ba-d41a-4062-a24a-1b811103ac29

import Mathlib
import Definitions.Def_PolarizedLearning_Model

open PolarizedLearning in
theorem solution (al : ℝ) (hal_lo : 1 / 2 < al) (hal_hi : al ≤ 1) :
    ∀ π ∈ Set.Ioo (0 : ℝ) 1, PolarizedLearning.f al π .low < PolarizedLearning.f al π .high := by
  rintro π ⟨h0, h1⟩
  simp only [PolarizedLearning.f, PolarizedLearning.g]
  have hD1 : 0 < π * al + (1 - π) * (1 - al) := by nlinarith
  have hD2 : 0 < π * (1 - al) + (1 - π) * al := by nlinarith
  have hg : π * (1 - al) / (π * (1 - al) + (1 - π) * al) <
      π * al / (π * al + (1 - π) * (1 - al)) := by
    rw [div_lt_div_iff₀ hD2 hD1]
    nlinarith [mul_pos (mul_pos h0 (sub_pos.2 h1)) (by linarith : (0:ℝ) < 2 * al - 1)]
  nlinarith [mul_pos (by linarith : (0:ℝ) < 2 * al - 1) (sub_pos.2 hg)]
