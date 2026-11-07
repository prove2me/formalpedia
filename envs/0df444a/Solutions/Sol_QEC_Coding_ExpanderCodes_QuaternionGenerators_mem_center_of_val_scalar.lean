-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.mem_center_of_val_scalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:31:09.447005+00:00
-- url     : https://prove2.me/submissions/27d7e3f8-928a-4596-8b02-a15b7a70cead

import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_alphaUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_baseUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_primeUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_baseUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution {epsilon y : K} (a : (Model epsilon y)ˣ)
    (r : K) (hScalar : (a : Model epsilon y) = (r : Model epsilon y)) :
    a ∈ Subgroup.center (Model epsilon y)ˣ := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Units.ext
  change (g : Model epsilon y) * (a : Model epsilon y) =
    (a : Model epsilon y) * (g : Model epsilon y)
  rw [hScalar]
  exact (QuaternionAlgebra.coe_commutes r (g : Model epsilon y)).symm
end QEC.Coding.ExpanderCodes.QuaternionGenerators
