-- Prove2me | solution 1 for boolToSign_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:00.162583+00:00
-- url     : https://prove2.me/submissions/9cd28216-7bb7-447f-833a-ea8fcaf180ac

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (b : Bool) : boolToSign b ^ 2 = 1 := by
  unfold boolToSign; cases b <;> norm_num
