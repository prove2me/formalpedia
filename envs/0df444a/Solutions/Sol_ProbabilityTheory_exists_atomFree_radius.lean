-- Prove2me | solution 1 for ProbabilityTheory.exists_atomFree_radius
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:47:14.894333+00:00
-- url     : https://prove2.me/submissions/b8c74e5e-c17c-44cf-a581-c87e409bef91

import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal

theorem solution (ν : Measure ℝ) [IsFiniteMeasure ν] {a b : ℝ} (hab : a < b) :
    ∃ r, r ∈ Set.Ioc a b ∧ ν {x | |x| = r} = 0 := by
  have key : Set.Countable {t : ℝ | 0 < ν {x : ℝ | |x| = t}} :=
    countable_meas_level_set_pos continuous_abs.measurable
  have aux : volume (Set.Ioc a b \ {t : ℝ | 0 < ν {x : ℝ | |x| = t}}) = volume (Set.Ioc a b) :=
    measure_sdiff_null (key.measure_zero volume)
  have len_pos : 0 < volume (Set.Ioc a b) := by
    rw [Real.volume_Ioc]
    simp only [ENNReal.ofReal_pos, sub_pos]
    exact hab
  rw [← aux] at len_pos
  obtain ⟨r, hr⟩ := nonempty_of_measure_ne_zero len_pos.ne'
  refine ⟨r, hr.1, ?_⟩
  exact le_antisymm (not_lt.mp hr.2) (zero_le)
