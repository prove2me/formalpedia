-- Prove2me | solution 1 for boolToSign_abs_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:34:24.008602+00:00
-- url     : https://prove2.me/submissions/71a66350-b637-4738-a334-cac3942af824

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (b : Bool) : |boolToSign b| = 1 := by
  unfold boolToSign; cases b <;> simp
