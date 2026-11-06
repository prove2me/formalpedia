-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_map_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:16:13.047694+00:00
-- url     : https://prove2.me/submissions/74e08854-c0a7-40c3-916f-b258d1d596d6

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_MatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialMatrixDerivation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_rationalDerivation_one_algebraMap_polynomial
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one


attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywisePolynomialDerivative_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
variable {k : Type*} [Field k]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution {n : Type*}
    [Fintype n] [DecidableEq n]
    (A : Matrix n n k[X]) :
    entrywiseMatrixDerivation
        (RatFuncDerivation.rationalDerivation
          (k := k) (M := RatFunc k) 1)
        ((algebraMap k[X] (RatFunc k)).mapMatrix A) =
      (algebraMap k[X] (RatFunc k)).mapMatrix
        (entrywisePolynomialDerivative A) := by
  ext i j
  simp only [entrywiseMatrixDerivation_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, entrywisePolynomialDerivative_apply]
  exact rationalDerivation_one_algebraMap_polynomial (A i j)
end QEC.Coding.AlgebraicGeometry
