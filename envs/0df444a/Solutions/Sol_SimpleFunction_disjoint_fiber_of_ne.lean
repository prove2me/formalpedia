-- Prove2me | solution 1 for SimpleFunction.disjoint_fiber_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:55:46.730023+00:00
-- url     : https://prove2.me/submissions/bd83f066-19b6-40b2-b6bf-895dfaa132d3

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

theorem solution (X : SimpleFunction Ω) {x y : EReal}
  (hxy : x ≠ y) :
    Disjoint (X ⁻¹' {x}) (X ⁻¹' {y}) := by
  refine Set.disjoint_left.2 ?_
  intro ω hx hy
  exact hxy <| by
    have hx' : X ω = x := by simpa using hx
    have hy' : X ω = y := by simpa using hy
    exact hx'.symm.trans hy'
end SimpleFunction
