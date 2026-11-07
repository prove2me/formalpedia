-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.z_mul_alpha
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:48:33.960666+00:00
-- url     : https://prove2.me/submissions/8a320428-536e-45df-ba53-c34c499723d6

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
theorem _root_.solution (epsilon y : K) : z epsilon y * alpha epsilon y =
    -(alpha epsilon y * z epsilon y) := by
  ext <;> simp [z, alpha]
end QEC.Coding.ExpanderCodes.QuaternionGenerators
