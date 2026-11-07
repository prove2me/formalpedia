-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.conjugate_sq_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:31:15.519074+00:00
-- url     : https://prove2.me/submissions/50c0a85c-47d0-4ff3-911b-512344e755b4

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
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_baseUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]
variable {H : Type*} [Group H]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (a t : H) (ha : a ^ 2 ≠ 1) :
    (t * a * t⁻¹) ^ 2 ≠ 1 := by
  intro hSquare
  apply ha
  rw [conj_pow] at hSquare
  have hCancel := congrArg (fun x => t⁻¹ * x * t) hSquare
  simpa [mul_assoc] using hCancel
end QEC.Coding.ExpanderCodes.QuaternionGenerators
