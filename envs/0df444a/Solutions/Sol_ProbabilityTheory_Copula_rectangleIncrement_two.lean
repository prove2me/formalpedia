-- Prove2me | solution 1 for ProbabilityTheory.Copula.rectangleIncrement_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:51:29.351258+00:00
-- url     : https://prove2.me/submissions/7c9b0cb6-0af8-4e6e-b1b1-bab8dc0fe2c4

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_Rectangle
public import Theorems.Thm_ProbabilityTheory_Copula_corner_empty
public import Theorems.Thm_ProbabilityTheory_Copula_partialIncrement_empty
public import Theorems.Thm_ProbabilityTheory_Copula_partialIncrement_insert
public import Theorems.Thm_ProbabilityTheory_Copula_partialIncrement_singleton
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
theorem _root_.solution (F : (Fin 2 → I) → ℝ) (a b : Fin 2 → I) :
    rectangleIncrement F a b = F b - F ![a 0, b 1] - F ![b 0, a 1] + F a := by
  have hu : (Finset.univ : Finset (Fin 2)) = insert 0 {1} := by decide
  rw [rectangleIncrement, hu, partialIncrement_insert _ _ _ _ _ (by decide),
    partialIncrement_singleton, partialIncrement_singleton]
  have h0 : Function.update b 0 (a 0) = ![a 0, b 1] := by
    funext i; fin_cases i <;> simp
  have h1 : Function.update b 1 (a 1) = ![b 0, a 1] := by
    funext i; fin_cases i <;> simp
  have h01 : Function.update (Function.update b 0 (a 0)) 1 (a 1) = a := by
    funext i; fin_cases i <;> simp
  rw [h01, h0, h1]
  ring
end ProbabilityTheory.Copula
