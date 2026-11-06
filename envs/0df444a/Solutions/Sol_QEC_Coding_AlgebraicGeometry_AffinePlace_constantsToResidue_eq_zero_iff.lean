-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.constantsToResidue_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:59.756647+00:00
-- url     : https://prove2.me/submissions/f66af277-3d8c-4e8e-876c-03bc5d6c4a02

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_constantsToResidue_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
open QEC.Coding.AlgebraicGeometry.AffinePlace
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
namespace QEC.Coding.AlgebraicGeometry.AffinePlace
theorem _root_.solution (P : carrier k F) (a : k) :
    constantsToResidue k F P a = 0 ↔
      algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) (Polynomial.C a) ∈
        P.asIdeal := by
  simpa only [constantsToResidue_apply] using
    (Ideal.algebraMap_residueField_eq_zero
      (R := _root_.FunctionField.ringOfIntegers k F) (I := P.asIdeal)
      (x := algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) (Polynomial.C a)))
end QEC.Coding.AlgebraicGeometry.AffinePlace
