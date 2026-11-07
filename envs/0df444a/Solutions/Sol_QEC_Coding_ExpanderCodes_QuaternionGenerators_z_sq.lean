-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.z_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:48:28.142639+00:00
-- url     : https://prove2.me/submissions/b31f8e44-76d7-4561-aae6-3b014fed9039

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
theorem _root_.solution (epsilon y : K) : z epsilon y ^ 2 = ((1 + y : K) : Model epsilon y) := by
  ext <;> simp [z, pow_two]
end QEC.Coding.ExpanderCodes.QuaternionGenerators
