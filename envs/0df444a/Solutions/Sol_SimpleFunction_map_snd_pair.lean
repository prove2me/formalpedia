-- Prove2me | solution 1 for SimpleFunction.map_snd_pair
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:54:34.723202+00:00
-- url     : https://prove2.me/submissions/948804ef-d73f-4e72-9518-0074d5131ccf

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
    (X.pair Y).map Prod.snd = Y := by
  simp [MeasureTheory.SimpleFunc.map_snd_pair X Y]
end SimpleFunction
