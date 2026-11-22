-- Prove2me | solution 1 for boolToSign_mul_abs_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:37:51.074801+00:00
-- url     : https://prove2.me/submissions/33be9ef6-04c7-463b-aa34-2455a7df1325

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Theorems.Thm_boolToSign_abs_eq_one

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (b₁ b₂ : Bool) : |boolToSign b₁ * boolToSign b₂| ≤ 1 := by
  rw [abs_mul, boolToSign_abs_eq_one, boolToSign_abs_eq_one, mul_one]
