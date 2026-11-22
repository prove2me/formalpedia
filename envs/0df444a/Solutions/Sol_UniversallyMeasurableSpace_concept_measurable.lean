-- Prove2me | solution 1 for UniversallyMeasurableSpace.concept_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:39:15.993357+00:00
-- url     : https://prove2.me/submissions/a0588782-af00-4605-a6ba-b2742433c595

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability

set_option autoImplicit true
@[expose] public section
public section
universe u
namespace UniversallyMeasurableSpace
theorem _root_.solution
    {X : Type u} [MeasurableSpace X] [h : UniversallyMeasurableSpace X]
    (c : Concept X Bool) : Measurable c :=
  h.all_concepts_measurable c
end UniversallyMeasurableSpace
