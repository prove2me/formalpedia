-- Prove2me | solution 1 for ProbabilityTheory.Copula.partialIncrement_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:50:29.311952+00:00
-- url     : https://prove2.me/submissions/84648e00-1f9a-447b-a978-d433a6eee667

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_Rectangle
public import Theorems.Thm_ProbabilityTheory_Copula_corner_empty
public import Theorems.Thm_ProbabilityTheory_Copula_partialIncrement_empty
public import Theorems.Thm_ProbabilityTheory_Copula_partialIncrement_insert
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


attribute [local simp] ProbabilityTheory.Copula.corner_empty
attribute [local simp] ProbabilityTheory.Copula.partialIncrement_empty

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval BigOperators
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (F : (Fin d → I) → ℝ) (a b : Fin d → I) (i : Fin d) :
    partialIncrement F a b {i} = F b - F (Function.update b i (a i)) := by
  change partialIncrement F a b (insert i ∅) = _
  rw [partialIncrement_insert _ _ _ _ _ (by simp)]
  simp
end ProbabilityTheory.Copula
