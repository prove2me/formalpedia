-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseAffinePlace.inverseChartRationalMap_eq_transported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:46:04.307307+00:00
-- url     : https://prove2.me/submissions/baee4ea1-9362-4625-b735-30348ead2960

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseChart
import Mathlib.FieldTheory.Separable
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_transportedRationalMap_X
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseChart_rationalMap_X


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
    (InverseChart.rationalMap k F).toRingHom = transportedRationalMap k F := by
  letI : Algebra k F := constantAlgebra k F
  letI : IsScalarTower k k⟮X⟯ F := constantScalarTower k F
  apply IsFractionRing.ringHom_ext (A := k[X])
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
  | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [map_mul, map_pow]
      rw [RatFunc.algebraMap_C, RatFunc.algebraMap_X]
      change InverseChart.rationalMap k F (RatFunc.C a) *
          InverseChart.rationalMap k F RatFunc.X ^ n =
        transportedRationalMap k F (RatFunc.C a) *
          transportedRationalMap k F RatFunc.X ^ n
      rw [InverseChart.rationalMap_X, transportedRationalMap_X]
      congr 1
      change ↑((InverseChart.rationalEquiv k F) (RatFunc.C a)) =
        algebraMap k⟮X⟯ F (rationalInvolution k (RatFunc.C a))
      rw [show RatFunc.C a = algebraMap k (RatFunc k) a from rfl,
        AlgEquiv.commutes, AlgEquiv.commutes]
      rfl
end QEC.Coding.AlgebraicGeometry.InverseAffinePlace
