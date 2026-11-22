-- Prove2me | solution 1 for ProbabilityTheory.measurePreserving_cdfUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:52.89119+00:00
-- url     : https://prove2.me/submissions/c5f60074-33c1-4821-b294-f43dcdb72e7f

module
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Definitions.Def_LeanPool_Copula_Distribution_ProbabilityIntegralTransform
public import Theorems.Thm_ProbabilityTheory_measurable_cdfUnit
public import Theorems.Thm_ProbabilityTheory_map_cdfUnit
attribute [local fun_prop] ProbabilityTheory.measurable_cdfUnit

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped unitInterval Topology
open ProbabilityTheory
namespace ProbabilityTheory
theorem _root_.solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : Continuous (cdf μ)) : MeasurePreserving (cdfUnit μ) μ volume :=
  ⟨measurable_cdfUnit μ, map_cdfUnit μ hc⟩
end ProbabilityTheory
