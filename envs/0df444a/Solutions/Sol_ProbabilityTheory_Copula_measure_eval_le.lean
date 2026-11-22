-- Prove2me | solution 1 for ProbabilityTheory.Copula.measure_eval_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:35.74239+00:00
-- url     : https://prove2.me/submissions/7f9b8ff5-185f-4537-87b2-879614a364a2

module
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Definitions.Def_LeanPool_Copula_Basic
public import Theorems.Thm_ProbabilityTheory_Copula_measure_preimage_eval

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open scoped unitInterval
open ProbabilityTheory
open ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (C : Copula d) (i : Fin d) (u : I) :
    C.toMeasure {x | x i ≤ u} = ENNReal.ofReal (u : ℝ) := by
  exact (C.measure_preimage_eval i measurableSet_Iic).trans (unitInterval.volume_Iic u)
end ProbabilityTheory.Copula
