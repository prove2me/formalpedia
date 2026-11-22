-- Prove2me | solution 1 for ProbabilityTheory.map_unitQuantile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:44:27.276268+00:00
-- url     : https://prove2.me/submissions/a901b8c0-3f12-4111-add1-727e8dc790d4

module
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.CDF
public import Definitions.Def_LeanPool_Copula_Distribution_Quantile
public import Theorems.Thm_ProbabilityTheory_measurable_unitQuantile
public import Theorems.Thm_ProbabilityTheory_unitQuantile_le_iff

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped unitInterval Topology
open ProbabilityTheory
namespace ProbabilityTheory
theorem _root_.solution (μ : Measure I) [IsProbabilityMeasure μ] :
    volume.map (unitQuantile μ) = μ := by
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply (measurable_unitQuantile μ) measurableSet_Iic]
  let u : I := ⟨μ.real (Iic x), measureReal_nonneg, measureReal_le_one⟩
  have he : unitQuantile μ ⁻¹' Iic x = Iic u := by
    ext t
    exact unitQuantile_le_iff μ t x
  rw [he, unitInterval.volume_Iic]
  exact ofReal_measureReal (measure_ne_top μ _)
end ProbabilityTheory
