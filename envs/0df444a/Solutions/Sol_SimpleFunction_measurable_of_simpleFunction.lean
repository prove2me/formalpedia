-- Prove2me | solution 1 for SimpleFunction.measurable_of_simpleFunction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:53:53.235726+00:00
-- url     : https://prove2.me/submissions/567610d7-8122-4261-a561-94663a47a25e

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

theorem solution (X : SimpleFunction Ω) : Measurable X :=
  MeasureTheory.SimpleFunc.measurable X
end SimpleFunction
