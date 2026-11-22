-- Prove2me | solution 1 for ProbabilityTheory.continuous_cdf_of_atomless
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:14.181218+00:00
-- url     : https://prove2.me/submissions/ba01a4b2-3108-4bd1-bcca-909c94ba55ed

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
theorem _root_.solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : Continuous (cdf μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [(cdf μ).rightLim_eq]
  apply le_antisymm ((monotone_cdf μ).leftLim_le le_rfl)
  have h := (cdf μ).measure_singleton x
  rw [measure_cdf, measure_singleton] at h
  exact sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp h.symm)
end ProbabilityTheory
