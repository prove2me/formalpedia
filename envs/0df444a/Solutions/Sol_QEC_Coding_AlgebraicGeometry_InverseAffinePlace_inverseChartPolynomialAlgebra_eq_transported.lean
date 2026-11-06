-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseAffinePlace.inverseChartPolynomialAlgebra_eq_transported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:27:28.65582+00:00
-- url     : https://prove2.me/submissions/a80914db-a590-479e-a1f9-547a6a211d2c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseChart
import Mathlib.FieldTheory.Separable
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_inverseChartPolynomialMap_eq_transported

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.InverseAffinePlace
open scoped IntermediateField Polynomial RatFunc
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
namespace QEC.Coding.AlgebraicGeometry.InverseAffinePlace
theorem _root_.solution :
    letI : Algebra k F := constantAlgebra k F
    letI : IsScalarTower k k⟮X⟯ F := constantScalarTower k F
    (InverseChart.polynomialMap k F).toAlgebra = transportedPolynomialAlgebra k F := by
  letI : Algebra k F := constantAlgebra k F
  letI : IsScalarTower k k⟮X⟯ F := constantScalarTower k F
  rw [show InverseChart.polynomialMap k F = transportedPolynomialMap k F from
    inverseChartPolynomialMap_eq_transported k F]
end QEC.Coding.AlgebraicGeometry.InverseAffinePlace
