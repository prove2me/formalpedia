-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension_add_placeDivisor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:48:34.520194+00:00
-- url     : https://prove2.me/submissions/c9c2d8c3-69c4-4da3-a26d-db2863616964

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrementDimension
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residueDegree_eq_finrank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochPlaceLeadingCoefficient_ker


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    [FiniteDimensional k (riemannRochSubmodule G)]
    [FiniteDimensional k (riemannRochSubmodule (G + placeDivisor P))] :
    riemannRochDimension (G + placeDivisor P) ≤
      riemannRochDimension G + residueDegree (k := k) (F := F) P := by
  letI : Algebra k P.residueField := residueAlgebra P
  letI : FiniteDimensional k P.residueField :=
    residueField_finiteDimensional P
  let leadingCoefficient := riemannRochPlaceLeadingCoefficient G P
  have hrank := leadingCoefficient.finrank_range_add_finrank_ker
  have hrange :
      Module.finrank k (LinearMap.range leadingCoefficient) ≤
        Module.finrank k P.residueField :=
    (LinearMap.range leadingCoefficient).finrank_le
  have hkernel :
      Module.finrank k (LinearMap.ker leadingCoefficient) =
        Module.finrank k (riemannRochPlaceIncrementSubmodule G P) := by
    rw [riemannRochPlaceLeadingCoefficient_ker]
  have hincrement :
      Module.finrank k (riemannRochSubmodule G) =
        Module.finrank k (riemannRochPlaceIncrementSubmodule G P) :=
    LinearEquiv.finrank_eq (riemannRochPlaceIncrementEquiv G P)
  have hresidue := residueDegree_eq_finrank P
  unfold riemannRochDimension
  omega
end QEC.Coding.AlgebraicGeometry.GlobalPlace
