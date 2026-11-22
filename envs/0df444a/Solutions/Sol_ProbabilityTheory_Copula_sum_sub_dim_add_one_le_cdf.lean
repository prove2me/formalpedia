-- Prove2me | solution 1 for ProbabilityTheory.Copula.sum_sub_dim_add_one_le_cdf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:48:11.98283+00:00
-- url     : https://prove2.me/submissions/d88dba5f-1f12-44af-be14-dbdcab1dcaa2

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_CDF_Bounds
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_dim_zero
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_update_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_zero
public import Theorems.Thm_ProbabilityTheory_Copula_ext
public import Theorems.Thm_ProbabilityTheory_Copula_map_eval
public import Theorems.Thm_ProbabilityTheory_Copula_measureReal_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_measure_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_measure_preimage_eval
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_ofMap
attribute [local simp] ProbabilityTheory.Copula.cdf_dim_zero
attribute [local simp] ProbabilityTheory.Copula.cdf_one
attribute [local simp] ProbabilityTheory.Copula.cdf_update_one
attribute [local simp] ProbabilityTheory.Copula.cdf_zero
attribute [local simp] ProbabilityTheory.Copula.map_eval
attribute [local simp] ProbabilityTheory.Copula.measureReal_eval_le
attribute [local simp] ProbabilityTheory.Copula.measure_eval_le
attribute [local simp] ProbabilityTheory.Copula.toMeasure_ofMap



set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval BigOperators
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (C : Copula d) (u : Fin d → I) :
    (∑ i, (u i : ℝ)) - d + 1 ≤ C.cdf u := by
  have hcomp : (Iic u)ᶜ = ⋃ i, {x | u i < x i} := by
    ext x
    simp [mem_Iic, Pi.le_def, not_forall, not_le]
  have hcoord (i : Fin d) : C.toMeasure.real {x | u i < x i} = 1 - (u i : ℝ) := by
    change (C.toMeasure ((fun x => x i) ⁻¹' Ioi (u i))).toReal = _
    rw [C.measure_preimage_eval i measurableSet_Ioi, unitInterval.volume_Ioi,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (u i).property.2)]
  have hunion := measureReal_iUnion_fintype_le (μ := C.toMeasure)
    (fun i : Fin d => {x | u i < x i})
  rw [← hcomp, measureReal_compl measurableSet_Iic, probReal_univ] at hunion
  simp_rw [hcoord] at hunion
  have h : 1 - C.cdf u ≤ (d : ℝ) - ∑ i, (u i : ℝ) := by
    simpa [cdf, Finset.sum_sub_distrib] using hunion
  linarith
end ProbabilityTheory.Copula
