-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.inverseXFibrePoint_residueDegree_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:19:21.793467+00:00
-- url     : https://prove2.me/submissions/a87bec60-e0ee-4800-8e60-3e7bf067ded8

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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_Rational_residueDegree_eq_one


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
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.inverseXIdealPrime
namespace QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces
theorem _root_.solution :
    letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
    letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
    AffinePlace.residueDegree K F inverseXFibrePoint.1 = 1 := by
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
  exact AffinePlace.Rational.residueDegree_eq_one K F inverseXFibrePointRational
end QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces
