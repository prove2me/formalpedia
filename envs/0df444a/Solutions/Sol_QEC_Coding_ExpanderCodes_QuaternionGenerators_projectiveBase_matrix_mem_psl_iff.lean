-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.projectiveBase_matrix_mem_psl_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:36:37.471209+00:00
-- url     : https://prove2.me/submissions/66bee705-1eb0-44fb-a7a3-22502a3267ce

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveDeterminant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.Algebra.Group.Units.Equiv
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionMatrix
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_det_base_matrix
import Theorems.Thm_QEC_Coding_ExpanderCodes_ProjectiveDeterminant_mk_mem_specialProjectiveSubgroup_iff_field_square


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]
open Matrix
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (r y : K) (hR : r ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    projectiveMatrixEquiv r y hR hOne hTwo (projectiveBase (r ^ 2) y hY hOne) ∈
      ProjectiveDeterminant.specialProjectiveSubgroup ↔
      ∃ s : K, s ^ 2 = y / (1 + y) := by
  change Matrix.ProjGenLinGroup.mk
    (Units.mapEquiv (matrixEquiv r y hR hOne hTwo).toMulEquiv
      (baseUnit (r ^ 2) y hY hOne)) ∈ _ ↔ _
  rw [ProjectiveDeterminant.mk_mem_specialProjectiveSubgroup_iff_field_square]
  change (∃ s : K, s ^ 2 = Matrix.det (matrixCoordinates r y (base (r ^ 2) y))) ↔ _
  rw [det_base_matrix r y hOne]
end QEC.Coding.ExpanderCodes.QuaternionGenerators
