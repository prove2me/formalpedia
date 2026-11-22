-- Prove2me | solution 1 for P2M_consistent_learner_pac__01cd7c3e2f93
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:44:42.233257+00:00
-- url     : https://prove2.me/submissions/b7b75db1-17b7-47a1-838a-faa6caebea23

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GeneralizationResults
public import Theorems.Thm_consistent_learner_pac
public import Theorems.Thm_MeasurableConceptClass_hWB
public import Theorems.Thm_MeasurableConceptClass_hc_meas


set_option autoImplicit true
@[expose] public section
public section
universe u
attribute [local instance] Classical.propDecidable
theorem _root_.solution (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) [MeasurableConceptClass X C] (hvcdim : VCDim X C < ⊤)
    (L : BatchLearner X Bool)
    (hcons : ∀ {m : ℕ} (S : Fin m → X × Bool), ∀ i, L.learn S (S i).1 = (S i).2) :
    PACLearnable X C :=
  consistent_learner_pac X C hvcdim
    (MeasurableConceptClass.hmeas_C C) (MeasurableConceptClass.hc_meas C)
    (MeasurableConceptClass.hWB C) L hcons
