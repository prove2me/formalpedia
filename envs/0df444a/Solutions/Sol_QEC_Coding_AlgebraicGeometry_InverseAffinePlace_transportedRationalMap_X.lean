-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseAffinePlace.transportedRationalMap_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:43:50.482113+00:00
-- url     : https://prove2.me/submissions/7ca4686f-6f6b-4212-a04e-8ca56226cd5e

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseChart
import Mathlib.FieldTheory.Separable
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_rationalInvolution_X

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
omit [Finite k]
namespace QEC.Coding.AlgebraicGeometry.InverseAffinePlace
theorem _root_.solution :
    transportedRationalMap k F RatFunc.X = InverseChart.inverseCoordinate k F := by
  change algebraMap k⟮X⟯ F (rationalInvolution k RatFunc.X) =
    InverseChart.inverseCoordinate k F
  rw [rationalInvolution_X, map_inv₀]
  rfl
end QEC.Coding.AlgebraicGeometry.InverseAffinePlace
