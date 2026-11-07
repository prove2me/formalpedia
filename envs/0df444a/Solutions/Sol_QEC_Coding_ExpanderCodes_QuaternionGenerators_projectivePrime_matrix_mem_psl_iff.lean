-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.projectivePrime_matrix_mem_psl_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:36:54.176698+00:00
-- url     : https://prove2.me/submissions/3d7cbb0d-6022-426c-a5c7-3a77f3d54c10

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveDeterminant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.Algebra.Group.Units.Equiv
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionMatrix
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectiveMatrixEquiv_mk
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_det_prime_matrix
import Theorems.Thm_QEC_Coding_ExpanderCodes_ProjectiveDeterminant_mk_mem_specialProjectiveSubgroup_iff_field_square
import Theorems.Thm_QEC_Coding_ExpanderCodes_ProjectiveDeterminant_toPGL_liftToPSL
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_alphaUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_baseUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_primeUnit
attribute [local simp] QEC.Coding.ExpanderCodes.ProjectiveDeterminant.toPGL_liftToPSL
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_baseUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit


attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.projectiveMatrixEquiv_mk

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]
open Matrix
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (r y : K) (hR : r ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    projectiveMatrixEquiv r y hR hOne hTwo
      (projectivePrime (r ^ 2) y (pow_ne_zero 2 hR) hY hOne) ∈
      ProjectiveDeterminant.specialProjectiveSubgroup ↔
      ∃ s : K, s ^ 2 = -(r ^ 2) * y / (1 + y) := by
  rw [show projectivePrime (r ^ 2) y (pow_ne_zero 2 hR) hY hOne =
    QuotientGroup.mk (primeUnit (r ^ 2) y (pow_ne_zero 2 hR) hY hOne) from rfl,
    projectiveMatrixEquiv_mk,
    ProjectiveDeterminant.mk_mem_specialProjectiveSubgroup_iff_field_square]
  change (∃ s : K, s ^ 2 = Matrix.det
    (matrixCoordinates r y (primeUnit (r ^ 2) y (pow_ne_zero 2 hR) hY hOne))) ↔ _
  rw [val_primeUnit, det_prime_matrix r y hOne]
end QEC.Coding.ExpanderCodes.QuaternionGenerators
