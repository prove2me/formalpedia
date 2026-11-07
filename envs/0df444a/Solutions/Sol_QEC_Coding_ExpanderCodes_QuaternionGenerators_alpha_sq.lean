-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.alpha_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:48:12.530949+00:00
-- url     : https://prove2.me/submissions/29228133-2f67-456f-b8c0-1c4081d95078

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
theorem _root_.solution (epsilon y : K) : alpha epsilon y ^ 2 = (epsilon : Model epsilon y) := by
  ext <;> simp [alpha, pow_two]
end QEC.Coding.ExpanderCodes.QuaternionGenerators
