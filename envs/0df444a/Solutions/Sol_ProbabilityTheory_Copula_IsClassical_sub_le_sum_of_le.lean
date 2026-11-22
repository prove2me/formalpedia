-- Prove2me | solution 1 for ProbabilityTheory.Copula.IsClassical.sub_le_sum_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:55:22.989323+00:00
-- url     : https://prove2.me/submissions/112e23c0-fd8e-4cf9-8969-94c3fdfac945

module
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Definitions.Def_LeanPool_Copula_Classical_Regularity
public import Theorems.Thm_ProbabilityTheory_Copula_IsClassical_update_sub_le
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
open Set
open scoped unitInterval BigOperators NNReal
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ} {F : (Fin d → I) → ℝ}
namespace ProbabilityTheory.Copula
namespace IsClassical
theorem _root_.solution (hF : IsClassical F) (a b : Fin d → I) (hab : a ≤ b) :
    F b - F a ≤ ∑ i, ((b i : ℝ) - (a i : ℝ)) := by
  have h (s : Finset (Fin d)) : F (s.piecewise b a) - F a ≤
      ∑ i ∈ s, ((b i : ℝ) - (a i : ℝ)) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.piecewise_empty, sub_self, Finset.sum_sub_distrib,
      Finset.sum_empty, Std.le_refl]
    | @insert i s hi ih =>
      have hx : s.piecewise b a i = a i := by simp only [hi, not_false_eq_true,
        Finset.piecewise_eq_of_notMem]
      have hs := hF.update_sub_le (s.piecewise b a) i (b i) (by rw [hx]; exact hab i)
      rw [Finset.piecewise_insert, Finset.sum_insert hi]
      rw [hx] at hs
      linarith
  simpa only [Finset.sum_sub_distrib, tsub_le_iff_right, ge_iff_le,
    Finset.piecewise_univ] using h Finset.univ
end IsClassical
end ProbabilityTheory.Copula
