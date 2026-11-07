-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.projectiveBase_sq_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:31:10.386513+00:00
-- url     : https://prove2.me/submissions/42b01fb6-76cd-4877-bad4-c6a9a6e8f465

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
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    projectiveBase epsilon y hY hOne ^ 2 ≠ 1 := by
  intro hSquare
  change ((baseUnit epsilon y hY hOne : ProjectiveGroup epsilon y) ^ 2) = 1 at hSquare
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hSquare
  have hCommute := Subgroup.mem_center_iff.mp hSquare (alphaUnit epsilon y hEpsilon)
  have hCoordinate := congrArg (fun a : (Model epsilon y)ˣ =>
    (a : Model epsilon y).imK) hCommute
  have hBaseSquare : ((baseUnit epsilon y hY hOne) ^ 2 : (Model epsilon y)ˣ) =
      baseUnit epsilon y hY hOne * baseUnit epsilon y hY hOne := pow_two _
  rw [hBaseSquare] at hCoordinate
  simp [alpha, base] at hCoordinate
  have hFour : (4 : K) = 0 := by
    field_simp at hCoordinate
    linear_combination -hCoordinate
  apply mul_ne_zero hTwo hTwo
  calc
    (2 : K) * 2 = 4 := by ring
    _ = 0 := hFour
end QEC.Coding.ExpanderCodes.QuaternionGenerators
