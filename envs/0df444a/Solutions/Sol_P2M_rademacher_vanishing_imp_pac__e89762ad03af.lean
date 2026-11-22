-- Prove2me | solution 1 for P2M_rademacher_vanishing_imp_pac__e89762ad03af
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:45:24.359385+00:00
-- url     : https://prove2.me/submissions/dbb849cb-b1d0-4b05-805e-1bf6788c841b

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GeneralizationResults
public import Theorems.Thm_rademacher_vanishing_imp_pac
public import Theorems.Thm_MeasurableConceptClass_hWB
public import Theorems.Thm_MeasurableConceptClass_hc_meas


set_option autoImplicit true
@[expose] public section
public section
universe u
attribute [local instance] Classical.propDecidable
theorem _root_.solution (X : Type u) [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) [MeasurableConceptClass X C]
    (hrad : ∀ ε > 0, ∃ m₀, ∀ (D : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure D →
      ∀ m ≥ m₀, RademacherComplexity X C D m < ε) :
    PACLearnable X C :=
  rademacher_vanishing_imp_pac X C
    (MeasurableConceptClass.hmeas_C C) (MeasurableConceptClass.hc_meas C)
    (MeasurableConceptClass.hWB C) hrad
