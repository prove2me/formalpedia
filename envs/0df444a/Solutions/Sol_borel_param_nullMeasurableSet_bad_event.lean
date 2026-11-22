-- Prove2me | solution 1 for borel_param_nullMeasurableSet_bad_event
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:44:05.815354+00:00
-- url     : https://prove2.me/submissions/5eb26c37-fc7d-4c6b-ab87-17b9d5471124

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_AnalyticMeasurability
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Theorems.Thm_borel_param_badEvent_analytic
public import Theorems.Thm_formalLearning_analyticSet_nullMeasurableSet_ghostPairs

set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory
theorem _root_.solution
    {X : Type u} [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (e : Θ → Concept X Bool)
    (he : Measurable (fun p : Θ × X => e p.1 p.2))
    (c : Concept X Bool) (hc : Measurable c)
    (m : ℕ) (ε : ℝ)
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D] :
    NullMeasurableSet (paramBadEvent e c m ε) (GhostPairMeasure D m) :=
  formalLearning_analyticSet_nullMeasurableSet_ghostPairs
    (borel_param_badEvent_analytic e he c hc m ε) D
