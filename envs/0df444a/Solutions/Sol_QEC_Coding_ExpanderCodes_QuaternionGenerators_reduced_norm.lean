-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.reduced_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:48:40.216704+00:00
-- url     : https://prove2.me/submissions/ed9e4af8-e86d-40e8-96c9-0d012bcf6781

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
theorem _root_.solution (epsilon y : K) (q : Model epsilon y) :
    (star q * q).re = q.re ^ 2 - epsilon * q.imI ^ 2 -
      (1 + y) * q.imJ ^ 2 + epsilon * (1 + y) * q.imK ^ 2 := by
  rcases q with ⟨a, b, c, d⟩
  simp
  ring
end QEC.Coding.ExpanderCodes.QuaternionGenerators
