-- Prove2me | solution 1 for ProbabilityTheory.Copula.measure_preimage_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:49.01618+00:00
-- url     : https://prove2.me/submissions/45b8a81d-246d-4296-8520-bc0c6f35f41f

module
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Definitions.Def_LeanPool_Copula_Basic
public import Theorems.Thm_ProbabilityTheory_Copula_map_eval
attribute [local simp] ProbabilityTheory.Copula.map_eval

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open scoped unitInterval
open ProbabilityTheory
open ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (C : Copula d) (i : Fin d) {s : Set I}
    (hs : MeasurableSet s) : C.toMeasure ((fun x => x i) ⁻¹' s) = volume s := by
  rw [← Measure.map_apply (measurable_pi_apply i) hs, C.map_eval]
end ProbabilityTheory.Copula
