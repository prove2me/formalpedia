-- Prove2me | solution 1 for ProbabilityTheory.Copula.measureReal_eval_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:44:22.505091+00:00
-- url     : https://prove2.me/submissions/b6d892f4-89a3-40e3-a442-cbae244970e4

module
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Definitions.Def_LeanPool_Copula_Basic
public import Theorems.Thm_ProbabilityTheory_Copula_ext
public import Theorems.Thm_ProbabilityTheory_Copula_map_eval
public import Theorems.Thm_ProbabilityTheory_Copula_measure_eval_le
attribute [local ext] ProbabilityTheory.Copula.ext
attribute [local simp] ProbabilityTheory.Copula.map_eval
attribute [local simp] ProbabilityTheory.Copula.measure_eval_le

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
    C.toMeasure.real {x | x i ≤ u} = (u : ℝ) := by
  simp [Measure.real, C.measure_eval_le, u.property.1]
end ProbabilityTheory.Copula
