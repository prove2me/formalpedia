-- Prove2me | solution 1 for boolToSign_abs_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:42:59.705992+00:00
-- url     : https://prove2.me/submissions/5c4ac9ce-3d68-43ea-875e-6ed60b110c88

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
theorem _root_.solution (b : Bool) : |boolToSign b| ≤ 1 := by
  rw [boolToSign_abs_eq_one]
