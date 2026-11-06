-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleFilterDiffDimension_add_placeDivisor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:49:50.611813+00:00
-- url     : https://prove2.me/submissions/97fb9785-134b-4030-8711-5a1a6d3bf0db

import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_Adele
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PlaceIncrementDimension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdelePlaceIncrement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleLocalLeadingCoefficient_ker
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleLocalLeadingCoefficient_surjective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residueDegree_eq_finrank


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
noncomputable section
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (D : Divisor (GlobalPlace k F)) (P : GlobalPlace k F) :
    globalAdeleFilterDiffDimension (k := k) (F := F) D (D + placeDivisor P) =
      residueDegree (k := k) (F := F) P := by
  letI : Algebra k P.residueField := residueAlgebra P
  letI : FiniteDimensional k P.residueField := residueField_finiteDimensional P
  letI : AddCommGroup
      (globalAdeleFilter (k := k) (F := F) (D + placeDivisor P)) :=
    Submodule.addCommGroup _
  letI : Module k
      (globalAdeleFilter (k := k) (F := F) (D + placeDivisor P)) :=
    Submodule.module _
  let f := globalAdeleLocalLeadingCoefficient (k := k) (F := F) D P
  have hker := globalAdeleLocalLeadingCoefficient_ker (k := k) (F := F) D P
  have hsurj := globalAdeleLocalLeadingCoefficient_surjective (k := k) (F := F) D P
  rw [globalAdeleFilterDiffDimension, ← hker]
  calc
    Module.finrank k
        (globalAdeleFilter (k := k) (F := F) (D + placeDivisor P) ⧸
          LinearMap.ker f) = Module.finrank k (LinearMap.range f) :=
      LinearEquiv.finrank_eq f.quotKerEquivRange
    _ = Module.finrank k P.residueField := by
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top]
    _ = residueDegree (k := k) (F := F) P :=
      (residueDegree_eq_finrank P).symm
end QEC.Coding.AlgebraicGeometry.GlobalPlace
