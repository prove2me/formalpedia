-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseAffinePlace.inverseChartPolynomialMap_eq_transported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:13:39.519585+00:00
-- url     : https://prove2.me/submissions/89c77c6e-1f38-4d7f-bcee-6892c526daa6

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseChart
import Mathlib.FieldTheory.Separable
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_inverseChartRationalMap_eq_transported

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
    (InverseChart.polynomialMap k F) = transportedPolynomialMap k F := by
  letI : Algebra k F := constantAlgebra k F
  letI : IsScalarTower k k⟮X⟯ F := constantScalarTower k F
  simp only [InverseChart.polynomialMap, transportedPolynomialMap]
  rw [inverseChartRationalMap_eq_transported k F]
end QEC.Coding.AlgebraicGeometry.InverseAffinePlace
