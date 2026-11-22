-- Prove2me | solution 1 for ProbabilityTheory.measurable_cdfUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:12.66612+00:00
-- url     : https://prove2.me/submissions/c98785f3-a4fe-4c11-89ef-4bad3b6648bb

module
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Definitions.Def_LeanPool_Copula_Distribution_ProbabilityIntegralTransform

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped unitInterval Topology
open ProbabilityTheory
namespace ProbabilityTheory
theorem _root_.solution (μ : Measure ℝ) : Measurable (cdfUnit μ) :=
  (monotone_cdf μ).measurable.subtype_mk
end ProbabilityTheory
