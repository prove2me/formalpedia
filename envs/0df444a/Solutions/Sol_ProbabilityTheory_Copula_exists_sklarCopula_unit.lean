-- Prove2me | solution 1 for ProbabilityTheory.Copula.exists_sklarCopula_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:46:25.684786+00:00
-- url     : https://prove2.me/submissions/010eb1f1-3d7a-44a2-b14d-683abec4b324

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_Distribution_Quantile
public import Definitions.Def_LeanPool_Copula_Sklar_Lift
public import Definitions.Def_LeanPool_Copula_Sklar_UnitInterval
public import Theorems.Thm_ProbabilityTheory_Copula_exists_lift
public import Theorems.Thm_ProbabilityTheory_Copula_ext
public import Theorems.Thm_ProbabilityTheory_map_unitQuantile
public import Theorems.Thm_ProbabilityTheory_measurable_unitQuantile
public import Theorems.Thm_ProbabilityTheory_unitQuantile_le_iff


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (μ : ProbabilityMeasure (Fin d → I)) :
    ∃ C : Copula d, ∀ x : Fin d → I,
      C.cdf (fun i => unitMarginalCDF μ i (x i)) = μ.toMeasure.real (Iic x) := by
  letI (i : Fin d) : IsProbabilityMeasure (μ.toMeasure.map (fun z => z i)) :=
    Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
  let q : Fin d → I → I := fun i => unitQuantile (μ.toMeasure.map (fun z => z i))
  have hq (i : Fin d) : Measurable (q i) := measurable_unitQuantile _
  obtain ⟨C, hC⟩ := exists_lift μ q hq (fun i => map_unitQuantile _)
  refine ⟨C, fun x => ?_⟩
  have hm : Measurable (fun u : Fin d → I => fun i => q i (u i)) :=
    measurable_pi_iff.mpr fun i => (hq i).comp (measurable_pi_apply i)
  have he : (fun u : Fin d → I => fun i => q i (u i)) ⁻¹' Iic x =
      Iic (fun i => unitMarginalCDF μ i (x i)) := by
    ext u
    change (∀ i, q i (u i) ≤ x i) ↔ ∀ i, u i ≤ unitMarginalCDF μ i (x i)
    exact forall_congr' fun i => unitQuantile_le_iff _ _ _
  rw [cdf, ← hC, map_measureReal_apply hm measurableSet_Iic, he]
end ProbabilityTheory.Copula
