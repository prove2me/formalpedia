-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.projectiveMatrixEquiv_mem_psl_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:49:18.221449+00:00
-- url     : https://prove2.me/submissions/f7c88f75-5044-4ec4-bc1d-a95bd6d89292

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveDeterminant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.Algebra.Group.Units.Equiv
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionMatrix
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_det_matrixCoordinates
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectiveMatrixEquiv_mk
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
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) (q : (Model (r ^ 2) y)ˣ) :
    projectiveMatrixEquiv r y hR hOne hTwo (QuotientGroup.mk q) ∈
      ProjectiveDeterminant.specialProjectiveSubgroup ↔
      ∃ s : K, s ^ 2 =
        (q : Model (r ^ 2) y).re ^ 2 - r ^ 2 * (q : Model (r ^ 2) y).imI ^ 2 -
          (1 + y) * (q : Model (r ^ 2) y).imJ ^ 2 +
          r ^ 2 * (1 + y) * (q : Model (r ^ 2) y).imK ^ 2 := by
  rw [projectiveMatrixEquiv_mk,
    ProjectiveDeterminant.mk_mem_specialProjectiveSubgroup_iff_field_square]
  change (∃ s : K, s ^ 2 = Matrix.det (matrixCoordinates r y (q : Model (r ^ 2) y))) ↔ _
  rw [det_matrixCoordinates]
end QEC.Coding.ExpanderCodes.QuaternionGenerators
