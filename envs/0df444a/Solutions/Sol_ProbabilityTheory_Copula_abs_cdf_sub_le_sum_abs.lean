-- Prove2me | solution 1 for ProbabilityTheory.Copula.abs_cdf_sub_le_sum_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:48:11.552204+00:00
-- url     : https://prove2.me/submissions/09f3faf5-89db-4d75-9067-1095910e8f3b

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_CDF_Continuity
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_sub_le_sum_abs
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_dim_zero
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_update_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_zero
public import Theorems.Thm_ProbabilityTheory_Copula_map_eval
public import Theorems.Thm_ProbabilityTheory_Copula_measureReal_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_measure_eval_le
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
open scoped unitInterval BigOperators NNReal
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (C : Copula d) (u v : Fin d → I) :
    |C.cdf u - C.cdf v| ≤ ∑ i, |(u i : ℝ) - (v i : ℝ)| := by
  refine abs_le.mpr ⟨?_, C.cdf_sub_le_sum_abs u v⟩
  have h : C.cdf v - C.cdf u ≤ ∑ i, |(u i : ℝ) - (v i : ℝ)| := by
    simpa only [abs_sub_comm] using C.cdf_sub_le_sum_abs v u
  linarith
end ProbabilityTheory.Copula
