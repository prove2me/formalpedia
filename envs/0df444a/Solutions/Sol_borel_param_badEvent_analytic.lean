-- Prove2me | solution 1 for borel_param_badEvent_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:41:41.375642+00:00
-- url     : https://prove2.me/submissions/09d7a689-7283-47c5-964b-07f2d9605d59

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_AnalyticMeasurability
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Theorems.Thm_paramWitnessSet_measurable

set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory
theorem _root_.solution
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [PolishSpace X]
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (e : Θ → Concept X Bool)
    (he : Measurable (fun p : Θ × X => e p.1 p.2))
    (c : Concept X Bool) (hc : Measurable c)
    (m : ℕ) (ε : ℝ) :
    MeasureTheory.AnalyticSet (paramBadEvent e c m ε) := by
  -- paramBadEvent = Prod.snd '' paramWitnessSet (by definition)
  change MeasureTheory.AnalyticSet (Prod.snd '' paramWitnessSet e c m ε)
  -- paramWitnessSet is MeasurableSet (Theorem A)
  have hW := paramWitnessSet_measurable e he c hc m ε
  -- SecondCountableTopology on range of Prod.snd
  -- range Prod.snd ⊆ GhostPairs X m which is SecondCountableTopology (from PolishSpace X)
  -- Any subtype of a SecondCountableTopology space inherits it
  have : SecondCountableTopology (Set.range (Prod.snd : Θ × GhostPairs X m → GhostPairs X m)) :=
    inferInstance
  exact hW.analyticSet_image measurable_snd
