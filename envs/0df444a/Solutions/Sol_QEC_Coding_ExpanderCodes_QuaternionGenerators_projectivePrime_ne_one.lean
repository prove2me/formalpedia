-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.projectivePrime_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:48:41.429806+00:00
-- url     : https://prove2.me/submissions/c387696a-6c24-4304-abc0-e991fe88b9a2

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
    projectivePrime epsilon y hEpsilon hY hOne ≠ 1 := by
  intro hIdentity
  change (primeUnit epsilon y hEpsilon hY hOne : ProjectiveGroup epsilon y) = 1
    at hIdentity
  rw [QuotientGroup.eq_one_iff] at hIdentity
  have hCommute := Subgroup.mem_center_iff.mp hIdentity (alphaUnit epsilon y hEpsilon)
  have hCoordinate := congrArg (fun a : (Model epsilon y)ˣ =>
    (a : Model epsilon y).imJ) hCommute
  simp [alpha, prime] at hCoordinate
  apply hTwo
  field_simp at hCoordinate
  linear_combination -hCoordinate
end QEC.Coding.ExpanderCodes.QuaternionGenerators
