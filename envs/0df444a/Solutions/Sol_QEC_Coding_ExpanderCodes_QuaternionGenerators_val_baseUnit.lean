-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.val_baseUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:44:03.508287+00:00
-- url     : https://prove2.me/submissions/b61ce4b0-c64e-4d4d-976a-0a1d052b1d8a

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
theorem _root_.solution (epsilon y : K) (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    (baseUnit epsilon y hY hOne : Model epsilon y) = base epsilon y := rfl
end QEC.Coding.ExpanderCodes.QuaternionGenerators
