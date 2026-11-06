-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.constantsToResidue_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:43:42.078201+00:00
-- url     : https://prove2.me/submissions/0414e571-862d-4c0f-8fb4-3dd03364833a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineResidue

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
    constantsToResidue k F P a =
      algebraMap (_root_.FunctionField.ringOfIntegers k F) (residueField k F P)
        (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) (Polynomial.C a)) :=
  rfl
end QEC.Coding.AlgebraicGeometry.AffinePlace
