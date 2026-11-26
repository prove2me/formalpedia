-- Prove2me | solution 1 for abs_numericalRadius_sub_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:24:21.77859+00:00
-- url     : https://prove2.me/submissions/1a721cd8-fb39-494e-bfaa-0e0b2aba1b6c

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Seminorm
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_NumericalRange_Radius
import Theorems.Thm_numericalRadius_neg
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_numericalRadius_le_norm
attribute [local simp] mem_numericalRange


attribute [local simp] numericalRadius_neg

set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A B : E →L[ℂ] E) :
    |numericalRadius A - numericalRadius B| ≤ ‖A - B‖ := by
  have hAB := numericalRadius_add_le (A - B) B
  rw [sub_add_cancel] at hAB
  have hBA := numericalRadius_add_le (B - A) A
  rw [sub_add_cancel] at hBA
  have hreverse : numericalRadius (B - A) = numericalRadius (A - B) := by
    rw [show B - A = -(A - B) by abel, numericalRadius_neg]
  have hdiff := numericalRadius_le_norm (A - B)
  rw [abs_sub_le_iff]
  constructor
  · linarith
  · rw [hreverse] at hBA
    linarith
