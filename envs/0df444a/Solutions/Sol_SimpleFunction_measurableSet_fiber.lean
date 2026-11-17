-- Prove2me | solution 1 for SimpleFunction.measurableSet_fiber
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:54:42.208999+00:00
-- url     : https://prove2.me/submissions/1ccc83eb-aac2-463d-ad40-6fcbded7a9da

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_1_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators
section SimpleFunction
open SimpleFunction
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution (X : SimpleFunction Ω) (x : EReal) :
    MeasurableSet (X ⁻¹' {x}) := by
  exact X.measurable (measurableSet_singleton x)
end SimpleFunction
