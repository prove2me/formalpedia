-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat26b_smearedMeasure_finite_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T07:49:16.492189+00:00
-- url     : https://prove2.me/submissions/b02f38fe-2535-4e91-9b69-0d7165518475

import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
import Theorems.Thm_ProbabilityTheory_leanlevy_chat26_lintegral_one_sub_sinc_public
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory ENNReal
open scoped NNReal ENNReal Real

variable (σ_sq : ℝ≥0)

theorem solution {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    IsFiniteMeasure (smearedMeasure σ_sq ν) := by
  refine ⟨?_⟩
  rw [smearedMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  refine ENNReal.add_lt_top.mpr
    ⟨?_, leanlevy_chat26_lintegral_one_sub_sinc_public hν⟩
  exact ENNReal.mul_lt_top (by simp [ENNReal.div_lt_top])
    (measure_lt_top _ _)
