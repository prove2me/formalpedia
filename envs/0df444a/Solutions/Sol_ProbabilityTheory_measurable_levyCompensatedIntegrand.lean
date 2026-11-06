-- Prove2me | solution 1 for ProbabilityTheory.measurable_levyCompensatedIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:18:51.686652+00:00
-- url     : https://prove2.me/submissions/84f05a9e-52f6-4676-906f-3aaac3b7a21f

import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ProbabilityTheory MeasureTheory Complex Set

theorem solution :
    ∀ (ξ : ℝ), Measurable (levyCompensatedIntegrand ξ) := by
  intro ξ
  unfold levyCompensatedIntegrand
  apply Measurable.sub
  · apply Measurable.sub
    · exact (((Complex.measurable_ofReal).mul measurable_const).mul measurable_const).cexp
    · exact measurable_const
  · apply Measurable.mul
    · exact (Complex.measurable_ofReal.mul measurable_const).mul measurable_const
    · exact measurable_const.ite
        (isOpen_Iio.preimage continuous_abs |>.measurableSet) measurable_const
