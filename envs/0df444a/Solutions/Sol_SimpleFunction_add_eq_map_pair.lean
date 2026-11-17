-- Prove2me | solution 1 for SimpleFunction.add_eq_map_pair
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:54:18.867734+00:00
-- url     : https://prove2.me/submissions/9fb2f34c-1a6a-4515-a3eb-fdcc47d78003

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

theorem solution (X Y : SimpleFunction Ω) :
    X + Y = (X.pair Y).map (fun p => p.1 + p.2) := by
  simpa using MeasureTheory.SimpleFunc.add_eq_map₂ X Y
end SimpleFunction
