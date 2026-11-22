-- Prove2me | solution 1 for ProbabilityTheory.Copula.partialIncrement_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:49:32.38279+00:00
-- url     : https://prove2.me/submissions/ef210ead-3221-4ab8-a403-65282663c06f

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_Rectangle
public import Theorems.Thm_ProbabilityTheory_Copula_corner_empty
public import Theorems.Thm_ProbabilityTheory_Copula_partialIncrement_empty
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
theorem _root_.solution (F : (Fin d → I) → ℝ) (a b : Fin d → I)
    (s : Finset (Fin d)) (i : Fin d) (hi : i ∉ s) :
    partialIncrement F a b (insert i s) =
      partialIncrement F a b s - partialIncrement F a (Function.update b i (a i)) s := by
  unfold partialIncrement
  rw [Finset.sum_powerset_insert hi, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have hit : i ∉ t := fun h => hi (Finset.mem_powerset.mp ht h)
  have hc : corner a b (insert i t) = corner a (Function.update b i (a i)) t := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [corner]
    · simp [corner, hji]
  rw [Finset.card_insert_of_notMem hit, pow_succ, hc]
  ring
end ProbabilityTheory.Copula
