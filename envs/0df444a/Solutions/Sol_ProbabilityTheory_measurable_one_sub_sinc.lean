-- Prove2me | solution 1 for ProbabilityTheory.measurable_one_sub_sinc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:24:30.688578+00:00
-- url     : https://prove2.me/submissions/40123b47-aac3-4cc3-b9b8-939c89c944da

import Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Measurability follows by composing the sinc function with continuous arithmetic. -/
theorem solution : Measurable fun x : ℝ => ENNReal.ofReal (1 - Real.sinc x) :=
  ENNReal.measurable_ofReal.comp (measurable_const.sub Real.measurable_sinc)
