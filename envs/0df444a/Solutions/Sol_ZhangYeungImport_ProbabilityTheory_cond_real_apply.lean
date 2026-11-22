-- Prove2me | solution 1 for ZhangYeungImport.ProbabilityTheory.cond_real_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:43:11.952888+00:00
-- url     : https://prove2.me/submissions/06739b8a-365c-4571-821e-485b7b63365d

module
public import Mathlib.Probability.ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
variable {Ω Ω' α : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {μ : Measure Ω}
  {s t : Set Ω}
open ProbabilityTheory
namespace ProbabilityTheory
theorem _root_.solution (hms : MeasurableSet s) (μ : Measure Ω) (t : Set Ω) :
    μ[|s].real t = (μ.real s)⁻¹ * μ.real (s ∩ t) := by
  simp [Measure.real, cond_apply hms]
end ProbabilityTheory
