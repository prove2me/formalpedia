-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport.transported_functionFieldDifferentialTrace_eq_rationalDifferentialInvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:47:03.419295+00:00
-- url     : https://prove2.me/submissions/f8489fd6-2f7f-47af-97da-a7b86fddedf7

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InvolutionResidueTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_DifferentialTraceTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseDifferentialTraceTransport_transported_fieldTrace_eq_rationalInvolution
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialCoordinate_differential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialTrace_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferential_eq_coordinate_smul_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_rationalInvolution_X
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_transportedRationalMap_X
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseRationalInfinityTransport_rationalDifferentialInvolution_differential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseRationalInfinityTransport_rationalDifferentialInvolution_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport
open scoped Polynomial RatFunc
open FunctionFieldDifferential
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport.directConstantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport.directConstantScalarTower
local notation3 "inverseRationalAlgebra" =>
  InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
local notation3 "inverseFunctionField" =>
  InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldFunctionField := oldFunctionField) k F
local notation3 "inverseIsSeparable" =>
  InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldSeparable := oldSeparable) k F
namespace QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport
theorem _root_.solution
    (omega : Differential k F) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : IsScalarTower k k⟮X⟯ F := inverseConstantScalarTower
      (oldPolynomialAlgebra := oldPolynomialAlgebra)
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldScalarTower := oldScalarTower) k F
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    functionFieldDifferentialTrace (k := k) (F := F) omega =
      InverseRationalInfinityTransport.rationalDifferentialInvolution (k := k)
        (letI : Algebra k⟮X⟯ F := oldRationalAlgebra
         letI : IsScalarTower k k⟮X⟯ F := directConstantScalarTower
           (oldPolynomialAlgebra := oldPolynomialAlgebra)
           (oldRationalAlgebra := oldRationalAlgebra)
           (oldScalarTower := oldScalarTower) k F
         letI : _root_.FunctionField k F := oldFunctionField
         letI : Algebra.IsSeparable k⟮X⟯ F := oldSeparable
         functionFieldDifferentialTrace (k := k) (F := F) omega) := by
  let oldCoordinate := functionFieldDifferentialCoordinate (k := k) (F := F)
  let oldGenerator := functionFieldDifferentialGenerator (k := k) (F := F)
  let oldTrace := functionFieldDifferentialTrace (k := k) (F := F)
  let x : F := algebraMap k⟮X⟯ F RatFunc.X
  have homega : omega = oldCoordinate omega • oldGenerator := by
    exact functionFieldDifferential_eq_coordinate_smul_generator
      (k := k) (F := F) omega
  letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
  letI : IsScalarTower k k⟮X⟯ F := inverseConstantScalarTower
    (oldPolynomialAlgebra := oldPolynomialAlgebra)
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldScalarTower := oldScalarTower) k F
  letI : _root_.FunctionField k F := inverseFunctionField
  letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
  let e := InverseAffinePlace.rationalInvolution k
  let q : RatFunc k := -((RatFunc.X : RatFunc k)⁻¹) ^ 2
  have hnewX : algebraMap k⟮X⟯ F RatFunc.X = x⁻¹ := by
    exact InverseAffinePlace.transportedRationalMap_X
      (oldRationalAlgebra := oldRationalAlgebra) k F
  have hcoordinateGenerator :
      functionFieldDifferentialCoordinate (k := k) (F := F) oldGenerator =
        -x ^ 2 := by
    change functionFieldDifferentialCoordinate (k := k) (F := F)
      (differential k F x) = -x ^ 2
    rw [functionFieldDifferentialCoordinate_differential]
    change functionFieldDerivation (k := k) (F := F) x = -x ^ 2
    rw [show x = (algebraMap k⟮X⟯ F RatFunc.X)⁻¹ by
      rw [hnewX, inv_inv],
      functionFieldDerivation_apply_inverseCoordinate, hnewX, inv_inv]
  have hq : algebraMap k⟮X⟯ F q = -x ^ 2 := by
    change (@algebraMap k⟮X⟯ F _ _ oldRationalAlgebra) (e q) = -x ^ 2
    dsimp only [q, e, x]
    rw [map_neg, map_pow, map_inv₀,
      InverseAffinePlace.rationalInvolution_X, inv_inv, map_neg, map_pow]
  have hcoordinate :
      functionFieldDifferentialCoordinate (k := k) (F := F) omega =
        algebraMap k⟮X⟯ F q * oldCoordinate omega := by
    calc
      functionFieldDifferentialCoordinate (k := k) (F := F) omega =
          functionFieldDifferentialCoordinate (k := k) (F := F)
            (oldCoordinate omega • oldGenerator) :=
        congrArg (functionFieldDifferentialCoordinate (k := k) (F := F)) homega
      _ = oldCoordinate omega *
          functionFieldDifferentialCoordinate (k := k) (F := F) oldGenerator := by
        rw [map_smul, smul_eq_mul]
      _ = algebraMap k⟮X⟯ F q * oldCoordinate omega := by
        rw [hcoordinateGenerator, hq]
        ring
  have htraceCoordinate :
      Algebra.trace k⟮X⟯ F
          (functionFieldDifferentialCoordinate (k := k) (F := F) omega) =
        q * e (@Algebra.trace k⟮X⟯ F _ _ oldRationalAlgebra
          (oldCoordinate omega)) := by
    rw [hcoordinate, ← Algebra.smul_def, map_smul]
    change q * Algebra.trace k⟮X⟯ F (oldCoordinate omega) = _
    rw [transported_fieldTrace_eq_rationalInvolution
      (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField)
      (oldSeparable := oldSeparable)]
  have hdInverse :
      differential k (RatFunc k) ((RatFunc.X : RatFunc k)⁻¹) =
        q • functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
    calc
      differential k (RatFunc k) ((RatFunc.X : RatFunc k)⁻¹) =
          functionFieldDifferentialCoordinate (k := k) (F := RatFunc k)
              (differential k (RatFunc k) ((RatFunc.X : RatFunc k)⁻¹)) •
            functionFieldDifferentialGenerator (k := k) (F := RatFunc k) :=
        functionFieldDifferential_eq_coordinate_smul_generator
          (k := k) (F := RatFunc k) _
      _ = q • functionFieldDifferentialGenerator
          (k := k) (F := RatFunc k) := by
        congr 1
        rw [functionFieldDifferentialCoordinate_differential]
        change functionFieldDerivation (k := k) (F := RatFunc k)
            ((algebraMap (RatFunc k) (RatFunc k) RatFunc.X)⁻¹) =
          -((algebraMap (RatFunc k) (RatFunc k) RatFunc.X)⁻¹) ^ 2
        exact functionFieldDerivation_apply_inverseCoordinate
          (k := k) (F := RatFunc k)
  change functionFieldDifferentialTrace (k := k) (F := F) omega =
    InverseRationalInfinityTransport.rationalDifferentialInvolution
      (k := k) (oldTrace omega)
  rw [functionFieldDifferentialTrace_apply, htraceCoordinate]
  change (q * e (@Algebra.trace k⟮X⟯ F _ _ oldRationalAlgebra
      (oldCoordinate omega))) •
      functionFieldDifferentialGenerator (k := k) (F := RatFunc k) =
    InverseRationalInfinityTransport.rationalDifferentialInvolution
      (k := k)
      ((@Algebra.trace k⟮X⟯ F _ _ oldRationalAlgebra
          (oldCoordinate omega)) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
  rw [InverseRationalInfinityTransport.rationalDifferentialInvolution_smul]
  change (q * e (@Algebra.trace k⟮X⟯ F _ _ oldRationalAlgebra
      (oldCoordinate omega))) •
      functionFieldDifferentialGenerator (k := k) (F := RatFunc k) =
    e (@Algebra.trace k⟮X⟯ F _ _ oldRationalAlgebra
        (oldCoordinate omega)) •
      InverseRationalInfinityTransport.rationalDifferentialInvolution
        (k := k)
        (differential k (RatFunc k) RatFunc.X)
  rw [InverseRationalInfinityTransport.rationalDifferentialInvolution_differential,
    InverseAffinePlace.rationalInvolution_X, hdInverse, smul_smul]
  congr 1
  ring
end QEC.Coding.AlgebraicGeometry.InverseDifferentialTraceTransport
