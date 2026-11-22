-- Prove2me | solution 1 for ProbabilityTheory.Copula.toMeasure_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:08.799041+00:00
-- url     : https://prove2.me/submissions/a77f054f-44f8-401c-b0c1-187a8f514a01

module
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Definitions.Def_LeanPool_Copula_Basic
public import Theorems.Thm_ProbabilityTheory_Copula_ext
attribute [local ext] ProbabilityTheory.Copula.ext

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open scoped unitInterval
open ProbabilityTheory
open ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution : Function.Injective (toMeasure (d := d)) :=
  fun _ _ h => ext h
end ProbabilityTheory.Copula
