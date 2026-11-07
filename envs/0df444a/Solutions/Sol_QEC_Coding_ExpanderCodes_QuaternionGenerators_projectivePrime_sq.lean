-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.projectivePrime_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:31:54.715694+00:00
-- url     : https://prove2.me/submissions/f29f2d96-bc67-4b46-abdf-dc9a245a14bd

import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_prime_sq
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_alphaUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_baseUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_primeUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_mem_center_of_val_scalar
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_baseUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    projectivePrime epsilon y hEpsilon hY hOne ^ 2 = 1 := by
  change ((primeUnit epsilon y hEpsilon hY hOne : ProjectiveGroup epsilon y) ^ 2) = 1
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  apply mem_center_of_val_scalar _ (epsilon * y / (1 + y))
  simpa using prime_sq epsilon y hOne
end QEC.Coding.ExpanderCodes.QuaternionGenerators
