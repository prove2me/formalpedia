-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.algebraMap_inverseIntegralClosureEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:04:44.024104+00:00
-- url     : https://prove2.me/submissions/3283ef7b-508c-404f-a73f-e8864f6830cc

import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Polynomial.Quotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalIntegralClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalFieldPlaces
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces
open scoped Polynomial RatFunc WithZero
open RatFuncFixtureDirectIntegralClosure
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces._p2m_local_instance_59938da7a3_22
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.oldRationalAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.oldPolynomialAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.oldScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.oldFunctionField
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.oldSeparable
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.oldFractionRing
namespace QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces
theorem _root_.solution (p : K[X]) :
    letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
    letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
    @algebraMap inverseB F _ _ inverseBToFAlgebra
        (inverseIntegralClosureEquiv p) =
      InverseAffinePlace.transportedPolynomialMap
        (oldRationalAlgebra := oldRationalAlgebra) K F p := by
  letI inverseBAlgebra : Algebra K[X] inverseB := inferInstance
  letI inverseBToF : Algebra inverseB F := inverseBToFAlgebra
  letI inverseBTower : @IsScalarTower K[X] inverseB F inverseBAlgebra.toSMul
      inverseBToF.toSMul
      (InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) K F).toSMul :=
    @IsScalarTower.of_algebraMap_eq K[X] inverseB F _ _ _ inverseBAlgebra inverseBToF
      (InverseAffinePlace.transportedPolynomialAlgebra
        (oldRationalAlgebra := oldRationalAlgebra) K F)
      (fun _ => rfl)
  have he : inverseIntegralClosureEquiv p = algebraMap K[X] inverseB p := by
    simpa using inverseIntegralClosureEquiv.commutes p
  calc
    @algebraMap inverseB F _ _ inverseBToFAlgebra (inverseIntegralClosureEquiv p) =
        @algebraMap inverseB F _ _ inverseBToFAlgebra (algebraMap K[X] inverseB p) := by
      rw [he]
    _ = @algebraMap K[X] F _ _
        (InverseAffinePlace.transportedPolynomialAlgebra
          (oldRationalAlgebra := oldRationalAlgebra) K F) p :=
      (@IsScalarTower.algebraMap_apply K[X] inverseB F _ _ _ inverseBAlgebra inverseBToF
        (InverseAffinePlace.transportedPolynomialAlgebra
          (oldRationalAlgebra := oldRationalAlgebra) K F) inverseBTower p).symm
    _ = InverseAffinePlace.transportedPolynomialMap
        (oldRationalAlgebra := oldRationalAlgebra) K F p := rfl
end QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces
