-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.alpha_mul_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:29:43.862457+00:00
-- url     : https://prove2.me/submissions/3ce8eed3-6923-4449-8d94-83dfcc90393f

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
theorem _root_.solution (epsilon y : K) : alpha epsilon y * base epsilon y =
    prime epsilon y := by
  ext <;> simp [alpha, base, prime]
end QEC.Coding.ExpanderCodes.QuaternionGenerators
