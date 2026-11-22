-- Prove2me | solution 1 for ProbabilityTheory.Copula.ClassicalConstruction.approximation_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:58:02.972144+00:00
-- url     : https://prove2.me/submissions/7084b562-307c-4576-9643-6d0a6098c228

module
public import Definitions.Def_LeanPool_Copula_Classical_Regularity
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Definitions.Def_LeanPool_Copula_Classical_Approximation
public import Theorems.Thm_ProbabilityTheory_Copula_ClassicalConstruction_Division_All_mono
public import Theorems.Thm_ProbabilityTheory_Copula_ClassicalConstruction_Division_grid_mesh
public import Theorems.Thm_ProbabilityTheory_Copula_ClassicalConstruction_cdf_probability_bounds
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_comonotonic
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_dim_zero
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_independence
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_update_one
public import Theorems.Thm_ProbabilityTheory_Copula_cdf_zero
public import Theorems.Thm_ProbabilityTheory_Copula_corner_empty
public import Theorems.Thm_ProbabilityTheory_Copula_map_eval
public import Theorems.Thm_ProbabilityTheory_Copula_measureReal_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_measure_eval_le
public import Theorems.Thm_ProbabilityTheory_Copula_partialIncrement_empty
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_comonotonic
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_independence
public import Theorems.Thm_ProbabilityTheory_Copula_toMeasure_ofMap
attribute [local simp] ProbabilityTheory.Copula.cdf_comonotonic
attribute [local simp] ProbabilityTheory.Copula.cdf_dim_zero
attribute [local simp] ProbabilityTheory.Copula.cdf_independence
attribute [local simp] ProbabilityTheory.Copula.cdf_one
attribute [local simp] ProbabilityTheory.Copula.cdf_update_one
attribute [local simp] ProbabilityTheory.Copula.cdf_zero
attribute [local simp] ProbabilityTheory.Copula.corner_empty
attribute [local simp] ProbabilityTheory.Copula.map_eval
attribute [local simp] ProbabilityTheory.Copula.measureReal_eval_le
attribute [local simp] ProbabilityTheory.Copula.measure_eval_le
attribute [local simp] ProbabilityTheory.Copula.partialIncrement_empty
attribute [local simp] ProbabilityTheory.Copula.toMeasure_comonotonic
attribute [local simp] ProbabilityTheory.Copula.toMeasure_independence
attribute [local simp] ProbabilityTheory.Copula.toMeasure_ofMap



set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval ENNReal BigOperators
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ} {F : (Fin d → I) → ℝ}
open ProbabilityTheory.Copula.ClassicalConstruction
namespace ProbabilityTheory.Copula.ClassicalConstruction
theorem _root_.solution (hF : IsClassical F) (n : ℕ) (u : Fin d → I) :
    F u - (d : ℝ) * (1 / 2 : ℝ) ^ n ≤ (approximation hF n).toMeasure.real (Iic u) ∧
      (approximation hF n).toMeasure.real (Iic u) ≤ F u := by
  apply cdf_probability_bounds hF _ (by positivity)
  apply (Division.grid_mesh _ _ _ _).mono
  intro a b hab i
  simpa only [one_div, inv_pow, tsub_le_iff_right, Icc.coe_one, Icc.coe_zero, sub_zero,
    List.count_flatten,
    List.map_replicate, List.count_finRange, List.sum_replicate, smul_eq_mul, mul_one,
      one_mul] using hab i
end ProbabilityTheory.Copula.ClassicalConstruction
