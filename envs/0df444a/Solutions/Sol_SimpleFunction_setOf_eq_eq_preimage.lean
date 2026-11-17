-- Prove2me | solution 1 for SimpleFunction.setOf_eq_eq_preimage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:54:58.530856+00:00
-- url     : https://prove2.me/submissions/e4647964-5748-4b16-8e0b-598897206320

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
    {ω | X ω = x} = X ⁻¹' {x} := by
  ext ω
  simp
end SimpleFunction
