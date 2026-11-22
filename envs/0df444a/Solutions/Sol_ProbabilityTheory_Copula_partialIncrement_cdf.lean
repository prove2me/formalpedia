-- Prove2me | solution 1 for ProbabilityTheory.Copula.partialIncrement_cdf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:50:29.700367+00:00
-- url     : https://prove2.me/submissions/b1e98de7-c4a3-45ee-8735-52c53f8ba2e7

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
public import Theorems.Thm_ProbabilityTheory_Copula_ext
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
theorem _root_.solution (C : Copula d) (a b : Fin d → I) (s : Finset (Fin d))
    (hab : a ≤ b) :
    partialIncrement C.cdf a b s = C.toMeasure.real {x | x ≤ b ∧ ∀ i ∈ s, a i < x i} := by
  induction s using Finset.induction_on generalizing b with
  | empty => simp [partialIncrement, cdf, Iic]
  | @insert i s hi ih =>
    have hab' : a ≤ Function.update b i (a i) := by
      intro j
      by_cases hji : j = i
      · subst j; simp
      · simpa [Function.update_of_ne hji] using hab j
    have hinter : {x | x ≤ b ∧ ∀ j ∈ s, a j < x j} ∩ {x | x i ≤ a i} =
        {x | x ≤ Function.update b i (a i) ∧ ∀ j ∈ s, a j < x j} := by
      ext x
      constructor
      · rintro ⟨⟨hxb, hx⟩, hxi⟩
        refine ⟨?_, hx⟩
        intro j
        by_cases hji : j = i
        · subst j; simpa using hxi
        · simpa [Function.update_of_ne hji] using hxb j
      · rintro ⟨hxb, hx⟩
        refine ⟨⟨?_, hx⟩, ?_⟩
        · intro j
          by_cases hji : j = i
          · subst j
            exact (by simpa using hxb i : x i ≤ a i).trans (hab i)
          · simpa [Function.update_of_ne hji] using hxb j
        · simpa using hxb i
    have hdiff : {x | x ≤ b ∧ ∀ j ∈ s, a j < x j} \ {x | x i ≤ a i} =
        {x | x ≤ b ∧ ∀ j ∈ insert i s, a j < x j} := by
      ext x
      simp only [mem_ofPred_eq, mem_sdiff, Finset.mem_insert, forall_eq_or_imp, not_le]
      tauto
    rw [partialIncrement_insert _ _ _ _ _ hi, ih b hab, ih _ hab']
    have h := measureReal_inter_add_sdiff (μ := C.toMeasure)
      (s := {x | x ≤ b ∧ ∀ j ∈ s, a j < x j}) (t := {x | x i ≤ a i})
      (measurableSet_le (measurable_pi_apply i) measurable_const)
    rw [hinter, hdiff] at h
    linarith
end ProbabilityTheory.Copula
