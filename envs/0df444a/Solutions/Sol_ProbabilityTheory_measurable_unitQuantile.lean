-- Prove2me | solution 1 for ProbabilityTheory.measurable_unitQuantile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:41.804772+00:00
-- url     : https://prove2.me/submissions/5c89fbc4-70f0-4767-a524-609f39cfeff0

module
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.CDF
public import Definitions.Def_LeanPool_Copula_Distribution_Quantile
public import Theorems.Thm_ProbabilityTheory_monotone_unitQuantile

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped unitInterval Topology
open ProbabilityTheory
namespace ProbabilityTheory
theorem _root_.solution (μ : Measure I) : Measurable (unitQuantile μ) :=
  (monotone_unitQuantile μ).measurable
end ProbabilityTheory
