-- Prove2me | solution 1 for borel_param_wellBehavedVCMeasTarget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:45:03.81489+00:00
-- url     : https://prove2.me/submissions/72d2a01c-21e4-4990-8097-ab4eae4e6e9e

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_AnalyticMeasurability
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Theorems.Thm_borel_param_nullMeasurableSet_bad_event

set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory
theorem _root_.solution
    {X : Type u} [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (e : Θ → Concept X Bool)
    (he : Measurable (fun p : Θ × X => e p.1 p.2)) :
    WellBehavedVCMeasTarget X (Set.range e) := by
  intro D _ c hc m ε
  have hEq :
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ Set.range e,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      = paramBadEvent e c m ε := by
    ext p
    simp only [paramBadEvent, paramWitnessSet, Set.mem_image, Set.mem_ofPred_eq, Prod.exists]
    constructor
    · rintro ⟨_, ⟨θ, rfl⟩, hp⟩; exact ⟨θ, p.1, p.2, hp, rfl⟩
    · rintro ⟨θ, s1, s2, hp, heq⟩
      have : (s1, s2) = p := Prod.ext (congrArg Prod.fst heq) (congrArg Prod.snd heq)
      subst this
      exact ⟨e θ, ⟨θ, rfl⟩, hp⟩
  rw [hEq]
  exact borel_param_nullMeasurableSet_bad_event e he c hc m ε D
