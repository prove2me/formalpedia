-- Prove2me | solution 1 for ProbabilityTheory.Copula.IsClassical.rectangleIncrement_mono_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:53:42.800542+00:00
-- url     : https://prove2.me/submissions/34b118ac-86f9-480d-ba9b-ac1bd235be93

module
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Definitions.Def_LeanPool_Copula_Classical_Regularity
public import Theorems.Thm_ProbabilityTheory_Copula_rectangleIncrement_split
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


section
public section
open Set
open scoped unitInterval BigOperators NNReal
namespace ProbabilityTheory.Copula
variable {d : ℕ} {F : (Fin d → I) → ℝ}
private theorem compare_by_updates (G : (Fin d → I) → ℝ) (a b : Fin d → I) (hab : a ≤ b)
    (hstep : ∀ x, a ≤ x → x ≤ b → ∀ i, G x ≤ G (Function.update x i (b i))) : G a ≤ G b := by
  have h (s : Finset (Fin d)) : G a ≤ G (s.piecewise b a) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.piecewise_empty, Std.le_refl]
    | @insert i s hi ih =>
      have ha : a ≤ s.piecewise b a := by
        intro j; by_cases hj : j ∈ s <;> simp only [Finset.piecewise, hj, ↓reduceIte, hab j,
          Std.le_refl]
      have hb : s.piecewise b a ≤ b := by
        intro j; by_cases hj : j ∈ s <;> simp only [Finset.piecewise, hj, ↓reduceIte, hab j,
          Std.le_refl]
      rw [Finset.piecewise_insert]
      exact ih.trans (hstep _ ha hb i)
  simpa only [ge_iff_le, Finset.piecewise_univ] using h Finset.univ
end ProbabilityTheory.Copula
end
end

set_option autoImplicit true
@[expose] public section
public section
open Set
open scoped unitInterval BigOperators NNReal
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ} {F : (Fin d → I) → ℝ}
namespace ProbabilityTheory.Copula
namespace IsClassical
theorem _root_.solution (hF : IsClassical F)
    (a b c : Fin d → I) (hab : a ≤ b) (hbc : b ≤ c) :
    rectangleIncrement F a b ≤ rectangleIncrement F a c := by
  apply compare_by_updates (rectangleIncrement F a) b c hbc
  intro x hbx hxc i
  have hsplit := rectangleIncrement_split (F := F) a (Function.update x i (c i)) i (x i)
  simp only [Function.update_idem, Function.update_eq_self] at hsplit
  have hnonneg := hF.increasing (Function.update a i (x i)) (Function.update x i (c i)) (by
    intro j
    by_cases hj : j = i
    · subst j; simpa only [Function.update_self] using hxc i
    · simpa only [Function.update_of_ne hj] using (hab j).trans (hbx j))
  linarith
end IsClassical
end ProbabilityTheory.Copula
