-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.rationalInfinity_residueDegree_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:46:09.866335+00:00
-- url     : https://prove2.me/submissions/6e6671d3-dc8c-451d-9ec4-3ea730561613

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncInverseInfinityValuation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncRationalInfinityDegreeTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residueDegree_eq_inverseFibre
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncFixturePlaces_inverseXFibrePoint_residueDegree_eq_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncInverseInfinityValuation_inverseXFibreGlobalPlace_eq_rationalInfinity


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces
open scoped Polynomial RatFunc WithZero
open RatFuncInverseInfinityValuation
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces._p2m_local_instance_137389a7d4_9
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.fixtureOldRationalAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.fixtureOldPolynomialAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.fixtureOldScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.fixtureOldFunctionField
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.fixtureOldSeparable
namespace QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces
theorem _root_.solution :
    GlobalPlace.residueDegree (k := K) (F := F) (GlobalPlace.rationalInfinity K) = 1 := by
  rw [GlobalPlace.residueDegree_eq_inverseFibre
    (P := GlobalPlace.rationalInfinity K) (D := inverseXFibrePoint) (by
      change (GlobalPlace.rationalInfinity K).valuation = inverseXFibreValuation
      exact (congrArg GlobalPlace.valuation
        inverseXFibreGlobalPlace_eq_rationalInfinity).symm)]
  letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := fixtureOldRationalAlgebra) K F
  letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := fixtureOldRationalAlgebra) K F
  letI : ratFuncRationalInfinityDegreeTransport_inverseScalarTowerType := InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := fixtureOldRationalAlgebra) K F
  letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := fixtureOldRationalAlgebra)
    (oldFunctionField := fixtureOldFunctionField) K F
  letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := fixtureOldRationalAlgebra)
    (oldSeparable := fixtureOldSeparable) K F
  change
    AffinePlace.residueDegree K F inverseXFibrePoint.1 = 1
  exact inverseXFibrePoint_residueDegree_eq_one
end QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces
