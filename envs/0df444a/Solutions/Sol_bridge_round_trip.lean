-- Prove2me | solution 1 for bridge_round_trip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:56.162689+00:00
-- url     : https://prove2.me/submissions/5b286458-ba1a-48ed-9892-ae3aa423306b

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
theorem _root_.solution (X : Type u) (C : ConceptClass X Bool) :
    setFamilyToConceptClass X (conceptClassToSetFamily X C) = C := by
  apply Set.ext
  intro c
  simp only [setFamilyToConceptClass, conceptClassToSetFamily, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨c', hc', hEq⟩
    have hcc' : c = c' := by
      funext x
      have := Set.ext_iff.mp hEq x
      simp only [Set.mem_ofPred_eq] at this
      cases hcx : c x <;> cases hc'x : c' x <;> simp_all
    rwa [hcc']
  · intro hc
    exact ⟨c, hc, rfl⟩
