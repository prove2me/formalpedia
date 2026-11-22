-- Prove2me | solution 1 for boolToSign_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:04.970396+00:00
-- url     : https://prove2.me/submissions/e786e95d-1958-485a-8a6a-7398c06b4361

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution : ∑ b : Bool, boolToSign b = 0 := by
  simp [boolToSign]
