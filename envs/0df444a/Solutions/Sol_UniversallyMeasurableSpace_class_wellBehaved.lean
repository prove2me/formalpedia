-- Prove2me | solution 1 for UniversallyMeasurableSpace.class_wellBehaved
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:39:16.38067+00:00
-- url     : https://prove2.me/submissions/0f438786-2335-47c0-97d1-4bc56ca5555f

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
    (C : ConceptClass X Bool) : WellBehavedVC X C :=
  h.all_classes_wellBehaved C
end UniversallyMeasurableSpace
