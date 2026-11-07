-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.det_prime_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:35:27.517148+00:00
-- url     : https://prove2.me/submissions/7b3c7a08-7ce6-424a-8ca8-424ec10b078b

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveDeterminant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.Algebra.Group.Units.Equiv
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionMatrix
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_det_matrixCoordinates
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectiveMatrixEquiv_mk
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
theorem _root_.solution (r y : K) (hOne : 1 + y ≠ 0) :
    Matrix.det (matrixCoordinates r y (prime (r ^ 2) y)) =
      -(r ^ 2) * y / (1 + y) := by
  rw [det_matrixCoordinates]
  simp [prime]
  field_simp
  ring
end QEC.Coding.ExpanderCodes.QuaternionGenerators
