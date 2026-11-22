-- Prove2me | solution 1 for ProbabilityTheory.Copula.exists_sklarCopula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:47:10.830056+00:00
-- url     : https://prove2.me/submissions/a6095723-73ab-4a63-b7ce-9b9eb52bf724

module
public import Definitions.Def_LeanPool_Copula_Sklar_Continuous
public import Definitions.Def_LeanPool_Copula_Sklar_UnitInterval
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Definitions.Def_LeanPool_Copula_Sklar_General
public import Theorems.Thm_ProbabilityTheory_Copula_exists_sklarCopula_unit
public import Theorems.Thm_ProbabilityTheory_Copula_ext


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (μ : ProbabilityMeasure (Fin d → ℝ)) :
    ∃ C : Copula d, IsSklarCopula μ C := by
  let T : (Fin d → ℝ) → Fin d → I := fun x i => unitInterval.sigmoid (x i)
  have hT : Measurable T := measurable_pi_iff.mpr fun i =>
    unitInterval.continuous_sigmoid.measurable.comp (measurable_pi_apply i)
  let ν : ProbabilityMeasure (Fin d → I) := μ.map hT.aemeasurable
  have hm (i : Fin d) : ν.toMeasure.map (fun z => z i) =
      (marginal μ i).map unitInterval.sigmoid := by
    change (μ.toMeasure.map T).map (fun z => z i) = _
    rw [Measure.map_map (measurable_pi_apply i) hT]
    exact (Measure.map_map unitInterval.continuous_sigmoid.measurable
      (measurable_pi_apply i)).symm
  have hF (i : Fin d) (x : ℝ) : unitMarginalCDF ν i (unitInterval.sigmoid x) =
      cdfUnit (marginal μ i) x := by
    apply Subtype.ext
    change (ν.toMeasure.map (fun z => z i)).real (Iic (unitInterval.sigmoid x)) =
      ProbabilityTheory.cdf (marginal μ i) x
    rw [hm, map_measureReal_apply unitInterval.continuous_sigmoid.measurable measurableSet_Iic]
    have he : unitInterval.sigmoid ⁻¹' Iic (unitInterval.sigmoid x) = Iic x := by
      ext y
      exact unitInterval.sigmoid_strictMono.le_iff_le
    rw [he, ProbabilityTheory.cdf_eq_real]
  obtain ⟨C, hC⟩ := exists_sklarCopula_unit ν
  refine ⟨C, fun x => ?_⟩
  have he : T ⁻¹' Iic (T x) = Iic x := by
    ext z
    change (∀ i, unitInterval.sigmoid (z i) ≤ unitInterval.sigmoid (x i)) ↔ ∀ i, z i ≤ x i
    exact forall_congr' fun _ => unitInterval.sigmoid_strictMono.le_iff_le
  have hfx : (fun i => unitMarginalCDF ν i (T x i)) = marginalTransform μ x :=
    funext fun i => hF i (x i)
  rw [← hfx, hC]
  change (μ.toMeasure.map T).real (Iic (T x)) = _
  rw [map_measureReal_apply hT measurableSet_Iic, he]
end ProbabilityTheory.Copula
