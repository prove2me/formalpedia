-- Prove2me | solution 1 for P2M_uc_does_not_imply_online__6055023e0fb5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:44:34.577387+00:00
-- url     : https://prove2.me/submissions/5bcf386a-927a-4dbf-a74f-2b86d873207f

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GeneralizationResults
public import Theorems.Thm_uc_does_not_imply_online
public import Theorems.Thm_UniversallyMeasurableSpace_class_wellBehaved
public import Theorems.Thm_UniversallyMeasurableSpace_concept_measurable


set_option autoImplicit true
@[expose] public section
public section
universe u
attribute [local instance] Classical.propDecidable
theorem _root_.solution (X : Type u) [MeasurableSpace X] [Infinite X]
    [UniversallyMeasurableSpace X] :
    ¬ (∀ (C : ConceptClass X Bool),
      HasUniformConvergence X C →
        ∃ (M : ℕ), MistakeBounded X Bool C M) :=
  uc_does_not_imply_online X
    (fun C => MeasurableConceptClass.hmeas_C C)
    (UniversallyMeasurableSpace.concept_measurable)
    (UniversallyMeasurableSpace.class_wellBehaved)
