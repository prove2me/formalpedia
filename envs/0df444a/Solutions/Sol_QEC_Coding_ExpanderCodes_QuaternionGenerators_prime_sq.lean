-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.prime_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:29:49.456431+00:00
-- url     : https://prove2.me/submissions/dff58740-2a9f-4562-b147-3c55f7ee9469

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
theorem _root_.solution (epsilon y : K) (hOne : 1 + y ≠ 0) :
    prime epsilon y ^ 2 = ((epsilon * y / (1 + y) : K) : Model epsilon y) := by
  ext <;> simp [prime, pow_two] <;> field_simp <;> ring
end QEC.Coding.ExpanderCodes.QuaternionGenerators
