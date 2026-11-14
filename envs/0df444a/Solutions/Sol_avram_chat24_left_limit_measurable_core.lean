-- Prove2me | solution 1 for avram_chat24_left_limit_measurable_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:05:43.58345+00:00
-- url     : https://prove2.me/submissions/11e6891e-fa6e-4281-9df6-24cd9330164c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_chat24_nnreal_left_continuous_borel_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

noncomputable section

theorem solution (f : ℝ≥0 → ℝ)
    (hf : ∀ t : ℝ≥0, 0 < t → ∃ l, Tendsto f (𝓝[<] t) (nhds l)) :
    Measurable (Function.leftLim f) := by
  apply AvramDividend.Classical.avram_chat24_nnreal_left_continuous_borel_measurable
    (Function.leftLim f)
  intro t
  apply continuousWithinAt_leftLim_Iic
  apply tendsto_leftLim_of_tendsto
  by_cases ht : 0 < t
  · exact hf t ht
  · have ht0 : t = 0 := le_antisymm (not_lt.mp ht) zero_le
    subst t
    refine ⟨f 0, ?_⟩
    simp

end
