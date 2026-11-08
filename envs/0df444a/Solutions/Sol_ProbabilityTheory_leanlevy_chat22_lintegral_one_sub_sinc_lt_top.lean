-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat22_lintegral_one_sub_sinc_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:48:28.754421+00:00
-- url     : https://prove2.me/submissions/4451f3db-7f56-49b0-99f3-2f4b6fc1cfbb

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_ProbabilityTheory_leanlevy_chat20_sinc_upper

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ENNReal ProbabilityTheory
open scoped NNReal ENNReal Real

/-- Source-exact sinc-deficit integrability, using the definition of a Lévy
measure directly instead of an unavailable private accessor theorem. -/
theorem solution {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    ∫⁻ x, ENNReal.ofReal (1 - Real.sinc x) ∂ν < ⊤ := by
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.min (measurable_id'.pow_const 2))
  calc
    ∫⁻ x, ENNReal.ofReal (1 - Real.sinc x) ∂ν
        ≤ ∫⁻ x, 2 * ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
          refine lintegral_mono fun x => ?_
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
            ← ENNReal.ofReal_mul (by norm_num)]
          exact ENNReal.ofReal_le_ofReal (leanlevy_chat20_sinc_upper x)
    _ = 2 * ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν :=
        lintegral_const_mul 2 hmeas
    _ < ⊤ := ENNReal.mul_lt_top (by norm_num) hν.2
