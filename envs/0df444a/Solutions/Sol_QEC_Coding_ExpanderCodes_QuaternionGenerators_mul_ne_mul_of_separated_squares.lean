-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.mul_ne_mul_of_separated_squares
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:31:12.343649+00:00
-- url     : https://prove2.me/submissions/774f90be-728b-42e0-89da-1cbfe1625514

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
theorem _root_.solution (a b g : H) (ha : a ^ 2 ≠ 1)
    (hb : b ^ 2 = 1) : a * g ≠ g * b := by
  intro hEqual
  have hConjugate : a = g * b * g⁻¹ := by
    calc
      a = a * g * g⁻¹ := by simp [mul_assoc]
      _ = g * b * g⁻¹ := by rw [hEqual]
  apply ha
  rw [hConjugate, conj_pow, hb]
  simp
end QEC.Coding.ExpanderCodes.QuaternionGenerators
