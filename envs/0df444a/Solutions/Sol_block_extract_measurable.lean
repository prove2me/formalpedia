-- Prove2me | solution 1 for block_extract_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:38:00.723629+00:00
-- url     : https://prove2.me/submissions/8ff85418-50fd-401e-b4cf-b469ee5d005f

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Probability.ProductMeasure
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution {X : Type*} [MeasurableSpace X]
    (k m : ℕ) (j : Fin k) :
    Measurable (fun (ω : Fin (k * m) → X) => blockExtract k m ω j) := by
  exact measurable_pi_iff.mpr (fun i => measurable_pi_apply _)
