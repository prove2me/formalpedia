-- Prove2me | solution 1 for ProbabilityTheory.exists_cdf_eq_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:27.367589+00:00
-- url     : https://prove2.me/submissions/b4727e04-823a-412a-b8bf-d877fb6b269c

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
theorem _root_.solution (μ : Measure ℝ) (hc : Continuous (cdf μ))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : ∃ x, cdf μ x = t := by
  exact mem_range_of_exists_le_of_exists_ge hc
    ((tendsto_cdf_atBot μ).eventually_le_const ht0).exists
    ((tendsto_cdf_atTop μ).eventually_const_le ht1).exists
end ProbabilityTheory
