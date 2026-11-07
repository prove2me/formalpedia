-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.det_matrixCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:32:32.778649+00:00
-- url     : https://prove2.me/submissions/aa9a334e-57b2-4d86-bf1e-399c59cf41c4

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveDeterminant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.Algebra.Group.Units.Equiv
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionMatrix
import Theorems.Thm_QEC_Coding_ExpanderCodes_ProjectiveDeterminant_toPGL_liftToPSL
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_alphaUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_baseUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_primeUnit
attribute [local simp] QEC.Coding.ExpanderCodes.ProjectiveDeterminant.toPGL_liftToPSL
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_baseUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]
open Matrix
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (r y : K) (q : Model (r ^ 2) y) :
    Matrix.det (matrixCoordinates r y q) =
      q.re ^ 2 - r ^ 2 * q.imI ^ 2 - (1 + y) * q.imJ ^ 2 +
        r ^ 2 * (1 + y) * q.imK ^ 2 := by
  simp [matrixCoordinates, Matrix.det_fin_two]
  ring
end QEC.Coding.ExpanderCodes.QuaternionGenerators
