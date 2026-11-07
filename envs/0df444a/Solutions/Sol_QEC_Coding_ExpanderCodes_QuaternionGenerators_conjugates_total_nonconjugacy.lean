-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.conjugates_total_nonconjugacy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:34:28.739307+00:00
-- url     : https://prove2.me/submissions/f44f9e7c-fe34-4eb3-bfbc-84b5a36d0865

import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_alphaUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_baseUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_primeUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectivePrime_sq
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectiveBase_sq_ne_one
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_mul_ne_mul_of_separated_squares
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_conjugate_sq_ne_one
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_baseUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (s t g : ProjectiveGroup epsilon y) :
    (s * projectiveBase epsilon y hY hOne * s⁻¹) * g ≠
      g * (t * projectivePrime epsilon y hEpsilon hY hOne * t⁻¹) := by
  apply mul_ne_mul_of_separated_squares
  · exact conjugate_sq_ne_one _ s
      (projectiveBase_sq_ne_one epsilon y hEpsilon hY hOne hTwo)
  · rw [conj_pow, projectivePrime_sq epsilon y hEpsilon hY hOne]
    simp
end QEC.Coding.ExpanderCodes.QuaternionGenerators
