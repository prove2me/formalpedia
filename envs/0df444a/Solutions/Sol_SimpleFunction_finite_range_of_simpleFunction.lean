-- Prove2me | solution 1 for SimpleFunction.finite_range_of_simpleFunction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:53:45.99431+00:00
-- url     : https://prove2.me/submissions/99fe4411-e14b-48d5-936d-476071b20c93

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

theorem solution (X : SimpleFunction Ω) : (Set.range X).Finite :=
  MeasureTheory.SimpleFunc.finite_range X
end SimpleFunction
