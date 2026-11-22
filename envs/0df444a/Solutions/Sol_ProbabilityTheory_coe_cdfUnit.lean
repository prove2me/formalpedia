-- Prove2me | solution 1 for ProbabilityTheory.coe_cdfUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:16.614882+00:00
-- url     : https://prove2.me/submissions/1beb31af-1e62-49d1-972e-559c49d7307a

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
theorem _root_.solution (μ : Measure ℝ) (x : ℝ) : (cdfUnit μ x : ℝ) = cdf μ x := rfl
end ProbabilityTheory
