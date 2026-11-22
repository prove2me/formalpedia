-- Prove2me | solution 1 for ProbabilityTheory.Copula.rectangleIncrement_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:52:37.363864+00:00
-- url     : https://prove2.me/submissions/dfdbaa4b-67b8-4c55-9479-55362dd98f2d

module
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Definitions.Def_LeanPool_Copula_Classical_Regularity
public import Theorems.Thm_ProbabilityTheory_Copula_partialIncrement_congr_lower
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
public import Theorems.Thm_ProbabilityTheory_Copula_partialIncrement_insert
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
open Set
open scoped unitInterval BigOperators NNReal
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ} {F : (Fin d → I) → ℝ}
namespace ProbabilityTheory.Copula
theorem _root_.solution (a b : Fin d → I) (i : Fin d) (t : I) :
    rectangleIncrement F a b =
      rectangleIncrement F a (Function.update b i t) +
        rectangleIncrement F (Function.update a i t) b := by
  let s := Finset.univ.erase i
  have hi : i ∉ s := by simp only [Finset.mem_erase, ne_eq, not_true_eq_false, Finset.mem_univ,
    and_true, not_false_eq_true, s]
  have hu : Finset.univ = insert i s := (Finset.insert_erase (Finset.mem_univ i)).symm
  have hl (c : Fin d → I) : partialIncrement F (Function.update a i t) c s =
      partialIncrement F a c s := partialIncrement_congr_lower _ _ _ _ (by
        intro j hj
        exact Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _)
  simp only [rectangleIncrement, hu, partialIncrement_insert _ _ _ _ _ hi,
    Function.update_self, Function.update_idem, hl]
  ring
end ProbabilityTheory.Copula
