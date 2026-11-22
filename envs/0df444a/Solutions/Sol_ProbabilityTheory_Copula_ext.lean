-- Prove2me | solution 1 for ProbabilityTheory.Copula.ext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:08.816276+00:00
-- url     : https://prove2.me/submissions/f481847a-3ed6-4321-9069-d9a6c840d7d8

module
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Definitions.Def_LeanPool_Copula_Basic

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open scoped unitInterval
open ProbabilityTheory
open ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution {C D : Copula d} (h : C.toMeasure = D.toMeasure) : C = D := by
  have hmeasure : C.measure = D.measure := ProbabilityMeasure.toMeasure_injective h
  cases C
  cases D
  cases hmeasure
  rfl
end ProbabilityTheory.Copula
