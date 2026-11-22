-- Prove2me | solution 1 for ProbabilityTheory.monotone_unitQuantile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:05.298291+00:00
-- url     : https://prove2.me/submissions/9fa05695-5acc-41ef-9de7-35005bd2cca0

module
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.CDF
public import Definitions.Def_LeanPool_Copula_Distribution_Quantile

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped unitInterval Topology
open ProbabilityTheory
namespace ProbabilityTheory
theorem _root_.solution (μ : Measure I) : Monotone (unitQuantile μ) := by
  intro t u htu
  exact sSup_le_sSup (fun _ hx => lt_of_lt_of_le hx (show (t : ℝ) ≤ (u : ℝ) from htu))
end ProbabilityTheory
