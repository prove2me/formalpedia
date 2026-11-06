-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.xZeroAffinePlace_intValuation_imageX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:50:30.926325+00:00
-- url     : https://prove2.me/submissions/9bd8634b-f5c5-4d1c-85ac-41b1c64c21d3

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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncFixturePlaces_xZeroIdeal_eq_span_imageX
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncFixturePlaces_directIntegralClosureEquiv_X_ne_zero

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
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.directConstantAlgebra
namespace QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces
theorem _root_.solution :
    xZeroAffinePlace.intValuation (directIntegralClosureEquiv Polynomial.X) =
      WithZero.exp (-1 : Int) :=
  xZeroAffinePlace.intValuation_singleton
    directIntegralClosureEquiv_X_ne_zero xZeroIdeal_eq_span_imageX
end QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces
