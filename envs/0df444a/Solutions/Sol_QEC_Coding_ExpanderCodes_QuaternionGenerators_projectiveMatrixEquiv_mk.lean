-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.projectiveMatrixEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:32:17.596733+00:00
-- url     : https://prove2.me/submissions/36c04377-6739-4055-90fa-59498c9bf6a9

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveDeterminant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.Algebra.Group.Units.Equiv
import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionMatrix

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]
open Matrix
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (r y : K) (hR : r ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) (q : (Model (r ^ 2) y)ˣ) :
    projectiveMatrixEquiv r y hR hOne hTwo (QuotientGroup.mk q) =
      Matrix.ProjGenLinGroup.mk
        (Units.mapEquiv (matrixEquiv r y hR hOne hTwo).toMulEquiv q) := rfl
end QEC.Coding.ExpanderCodes.QuaternionGenerators
