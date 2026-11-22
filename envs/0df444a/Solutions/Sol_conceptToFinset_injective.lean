-- Prove2me | solution 1 for conceptToFinset_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:57.757918+00:00
-- url     : https://prove2.me/submissions/dad855c4-d596-4de0-b666-b607d21b70b8

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Data
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Ordinal
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Bayesian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Bridge

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution {X : Type u} [Fintype X] :
    Function.Injective (conceptToFinset (X := X)) := by
  intro c₁ c₂ h
  funext x
  have : x ∈ conceptToFinset c₁ ↔ x ∈ conceptToFinset c₂ := by rw [h]
  simp only [conceptToFinset, Finset.mem_filter, Finset.mem_univ, true_and] at this
  cases hc₁ : c₁ x <;> cases hc₂ : c₂ x <;> simp_all
