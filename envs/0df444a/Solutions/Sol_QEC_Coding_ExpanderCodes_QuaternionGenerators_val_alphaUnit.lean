-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:44:02.681075+00:00
-- url     : https://prove2.me/submissions/9761e5f4-3e6b-41e6-a689-b48fb2971fac

import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (epsilon y : K) (hEpsilon : epsilon ≠ 0) :
    (alphaUnit epsilon y hEpsilon : Model epsilon y) = alpha epsilon y := rfl
end QEC.Coding.ExpanderCodes.QuaternionGenerators
