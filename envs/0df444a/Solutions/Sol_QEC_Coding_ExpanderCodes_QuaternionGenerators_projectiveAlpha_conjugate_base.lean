-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.projectiveAlpha_conjugate_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:31:56.706642+00:00
-- url     : https://prove2.me/submissions/180500a4-f6b7-44f0-a5d6-71836cdaaff2

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionCayleySets
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_mem_center_of_val_scalar
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
theorem _root_.solution (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) :
    projectiveAlpha epsilon y hEpsilon * projectiveBase epsilon y hY hOne *
      (projectiveAlpha epsilon y hEpsilon)⁻¹ =
        (projectiveBase epsilon y hY hOne)⁻¹ := by
  have hScalar :
      ((alphaUnit epsilon y hEpsilon * baseUnit epsilon y hY hOne *
        (alphaUnit epsilon y hEpsilon)⁻¹ * baseUnit epsilon y hY hOne) :
          Model epsilon y) = ((y / (1 + y) : K) : Model epsilon y) := by
    ext <;> simp [alphaUnit, baseUnit, alpha, base] <;> field_simp <;> ring
  have hCentral := mem_center_of_val_scalar
    (alphaUnit epsilon y hEpsilon * baseUnit epsilon y hY hOne *
      (alphaUnit epsilon y hEpsilon)⁻¹ * baseUnit epsilon y hY hOne)
    (y / (1 + y)) hScalar
  have hProduct := (QuotientGroup.eq_one_iff _).mpr hCentral
  apply mul_eq_one_iff_eq_inv.mp
  simpa [projectiveAlpha, projectiveBase, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv] using hProduct
end QEC.Coding.ExpanderCodes.QuaternionGenerators
