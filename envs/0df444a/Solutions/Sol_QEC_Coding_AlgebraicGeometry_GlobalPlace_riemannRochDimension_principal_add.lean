-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension_principal_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:25:27.217612+00:00
-- url     : https://prove2.me/submissions/3f4d5172-fe83-494f-b265-04c167d48cd5

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Dimension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PrincipalShift

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (u : Fˣ) (G : Divisor (GlobalPlace k F))
    [FiniteDimensional k
      (riemannRochSubmodule
        (GlobalPlace.principalDivisor (k := k) (F := F) u + G))]
    [FiniteDimensional k (riemannRochSubmodule G)] :
    riemannRochDimension
        (GlobalPlace.principalDivisor (k := k) (F := F) u + G) =
      riemannRochDimension G := by
  unfold riemannRochDimension
  exact LinearEquiv.finrank_eq
    (riemannRochSubmodule_principal_add_equiv (k := k) (F := F) u G)
end QEC.Coding.AlgebraicGeometry.GlobalPlace
