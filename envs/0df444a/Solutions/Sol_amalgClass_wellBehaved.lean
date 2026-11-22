-- Prove2me | solution 1 for amalgClass_wellBehaved
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:46:09.416663+00:00
-- url     : https://prove2.me/submissions/223b25d6-3185-43b4-bcf7-20a269363efe

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Interpolation
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Amalgamation
public import Theorems.Thm_measurableSet_agreementRel
public import Theorems.Thm_borel_param_wellBehavedVCMeasTarget


set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory
theorem _root_.solution
    {X : Type u}
    [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ₁ Θ₂ S : Type*}
    [MeasurableSpace Θ₁] [StandardBorelSpace Θ₁]
    [MeasurableSpace Θ₂] [StandardBorelSpace Θ₂]
    [MeasurableSpace S] [StandardBorelSpace S]
    (π₁ : Θ₁ → S) (π₂ : Θ₂ → S)
    (hπ₁ : Measurable π₁) (hπ₂ : Measurable π₂)
    (merge : Θ₁ × Θ₂ → Concept X Bool)
    (hmerge : Measurable (fun p : (Θ₁ × Θ₂) × X => merge p.1 p.2)) :
    WellBehavedVCMeasTarget X (amalgClass π₁ π₂ merge) := by
  have hmeas := measurableSet_agreementRel π₁ π₂ hπ₁ hπ₂
  have := hmeas.standardBorel
  have hrange : amalgClass π₁ π₂ merge =
      Set.range (fun θ : ↥(agreementRel π₁ π₂) => merge θ.val) := by
    ext h
    simp only [amalgClass, relParamClass, Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨θ, hθ, rfl⟩; exact ⟨⟨θ, hθ⟩, rfl⟩
    · rintro ⟨⟨θ, hθ⟩, rfl⟩; exact ⟨θ, hθ, rfl⟩
  have he : Measurable (fun p : ↥(agreementRel π₁ π₂) × X =>
      (fun θ : ↥(agreementRel π₁ π₂) => merge θ.val) p.1 p.2) :=
    hmerge.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  rw [hrange]
  exact borel_param_wellBehavedVCMeasTarget _ he
