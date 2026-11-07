-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:30:33.080627+00:00
-- url     : https://prove2.me/submissions/b9c6ace9-f216-46b3-b891-940d65f8e027

import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_alpha_mul_base

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    (primeUnit epsilon y hEpsilon hY hOne : Model epsilon y) = prime epsilon y := by
  exact alpha_mul_base epsilon y
end QEC.Coding.ExpanderCodes.QuaternionGenerators
