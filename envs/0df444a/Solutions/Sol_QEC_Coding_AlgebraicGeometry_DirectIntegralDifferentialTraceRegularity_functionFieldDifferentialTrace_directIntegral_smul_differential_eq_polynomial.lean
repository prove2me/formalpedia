-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity.functionFieldDifferentialTrace_directIntegral_smul_differential_eq_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:44:08.217348+00:00
-- url     : https://prove2.me/submissions/5f4cc7dc-3d80-4195-ae44-83e95732f896

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SmithDifferentialTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialTraceRegularity
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_derivation_logarithmic_trace_eq_matrix_trace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialCoordinate_differential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialTrace_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicIdealResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_map_polynomial
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywiseMatrixDerivation_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_entrywisePolynomialDerivative_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicIdealResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_add
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywiseMatrixDerivation_one
attribute [local simp] QEC.Coding.AlgebraicGeometry.entrywisePolynomialDerivative_apply


section
open scoped Polynomial RatFunc nonZeroDivisors
namespace QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity
open QEC.Coding.AlgebraicGeometry
open FunctionFieldDifferential
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] integralDifferentialTraceRegularity_constantAlgebra
attribute [local instance] integralDifferentialTraceRegularity_scalarTower
omit [Finite k] in
private theorem functionFieldDerivation_extends_rationalDerivation
    (c : RatFunc k) :
    functionFieldDerivation (k := k) (F := F)
        (algebraMap (RatFunc k) F c) =
      algebraMap (RatFunc k) F
        (RatFuncDerivation.rationalDerivation
          (k := k) (M := RatFunc k) 1 c) := by
  let D₀ := RatFuncDerivation.rationalDerivation
    (k := k) (M := RatFunc k) 1
  rw [functionFieldDerivation,
    SeparableDerivationExtension.separableDerivationExtension_apply_algebraMap]
  let Dmap : Derivation k (RatFunc k) F :=
    (Algebra.ofId (RatFunc k) F).toLinearMap.compDer D₀
  have hmap :
      RatFuncDerivation.rationalDerivation (k := k) (M := F) 1 = Dmap := by
    have hX : Dmap RatFunc.X = (1 : F) := by
      change algebraMap (RatFunc k) F
        (RatFuncDerivation.rationalDerivation
          (k := k) (M := RatFunc k) 1 RatFunc.X) = 1
      rw [RatFuncDerivation.rationalDerivation_apply_X, map_one]
    rw [← hX]
    exact RatFuncDerivation.rationalDerivation_eq_of_apply_X (k := k)
  have hc := Derivation.congr_fun hmap c
  change RatFuncDerivation.rationalDerivation (k := k) (M := F) 1 c =
    algebraMap (RatFunc k) F (D₀ c) at hc
  exact hc
omit [Finite k] in
private theorem derivation_weighted_trace_eq_matrix_trace
    {K L : Type*} [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L]
    (D₀ : Derivation k K K) (D : Derivation k L L)
    (hD : ∀ c : K, D (algebraMap K L c) = algebraMap K L (D₀ c))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (basis : Module.Basis ι K L)
    (r t : L) :
    Algebra.trace K L (r * D t) =
      Matrix.trace
        (LinearMap.toMatrix basis basis (Algebra.lmul K L r) *
          entrywiseMatrixDerivation D₀
            (LinearMap.toMatrix basis basis (Algebra.lmul K L t))) := by
  classical
  by_cases ht : t = 0
  · subst t
    have hzeroDerivative :
        entrywiseMatrixDerivation D₀ (0 : Matrix ι ι K) = 0 := by
      ext i j
      simp [entrywiseMatrixDerivation_apply]
    simp only [map_zero, mul_zero, hzeroDerivative, Matrix.trace_zero]
  · have hlog :=
      FunctionFieldDifferential.derivation_logarithmic_trace_eq_matrix_trace
        D₀ D hD basis (r * t) t ht
    have hleft : (r * t) * D t * t⁻¹ = r * D t := by
      field_simp [ht]
    have hmatrix :
        LinearMap.toMatrix basis basis (Algebra.lmul K L (r * t)) *
            LinearMap.toMatrix basis basis (Algebra.lmul K L t⁻¹) =
          LinearMap.toMatrix basis basis (Algebra.lmul K L r) := by
      rw [← LinearMap.toMatrix_mul, ← map_mul]
      congr 1
      field_simp [ht]
    rw [hleft] at hlog
    simpa only [hmatrix] using hlog
end QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity
end

set_option autoImplicit false
open scoped Polynomial RatFunc nonZeroDivisors
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity
open QEC.Coding.AlgebraicGeometry
open FunctionFieldDifferential
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity.integralDifferentialTraceRegularity_constantAlgebra
attribute [local instance] integralDifferentialTraceRegularity_constantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity.integralDifferentialTraceRegularity_scalarTower
attribute [local instance] integralDifferentialTraceRegularity_scalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity._p2m_local_instance_828a280e13_54
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity._p2m_local_instance_828a280e13_58
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity._p2m_local_instance_828a280e13_61
namespace QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity
theorem _root_.solution
    (b t : B k F) :
    functionFieldDifferentialTrace (k := k) (F := F)
        ((algebraMap (B k F) F b) •
          differential k F (algebraMap (B k F) F t)) =
      algebraMap (R k) (RatFunc k)
          (directIntegralDifferentialTracePolynomial k F b t) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
  classical
  let basis := Module.finBasis (R k) (B k F)
  let basisF := basis.localizationLocalization
    (RatFunc k) (R k)⁰ F
  let m := algebraMap (R k) (RatFunc k)
  let D₀ := RatFuncDerivation.rationalDerivation
    (k := k) (M := RatFunc k) 1
  let D := functionFieldDerivation (k := k) (F := F)
  let Bmat : Matrix _ _ (R k) :=
    LinearMap.toMatrix basis basis (Algebra.lmul (R k) (B k F) b)
  let Tmat : Matrix _ _ (R k) :=
    LinearMap.toMatrix basis basis (Algebra.lmul (R k) (B k F) t)
  let BF : Matrix _ _ (RatFunc k) := m.mapMatrix Bmat
  let TF : Matrix _ _ (RatFunc k) := m.mapMatrix Tmat
  have hBF :
      LinearMap.toMatrix basisF basisF
          (Algebra.lmul (RatFunc k) F (algebraMap (B k F) F b)) = BF := by
    symm
    exact Algebra.map_leftMulMatrix_localization
      (Rₘ := RatFunc k) (Sₘ := F) (R k) (R k)⁰ basis b
  have hTF :
      LinearMap.toMatrix basisF basisF
          (Algebra.lmul (RatFunc k) F (algebraMap (B k F) F t)) = TF := by
    symm
    exact Algebra.map_leftMulMatrix_localization
      (Rₘ := RatFunc k) (Sₘ := F) (R k) (R k)⁰ basis t
  have htrace := derivation_weighted_trace_eq_matrix_trace (k := k)
    D₀ D (functionFieldDerivation_extends_rationalDerivation (k := k) (F := F))
    basisF (algebraMap (B k F) F b) (algebraMap (B k F) F t)
  have hentrywise :
      entrywiseMatrixDerivation D₀ TF =
        m.mapMatrix (entrywisePolynomialDerivative Tmat) := by
    change entrywiseMatrixDerivation
        (RatFuncDerivation.rationalDerivation
          (k := k) (M := RatFunc k) 1)
        (m.mapMatrix Tmat) = _
    exact entrywiseMatrixDerivation_map_polynomial Tmat
  have hmatrix :
      Matrix.trace (BF * entrywiseMatrixDerivation D₀ TF) =
        m (Matrix.trace (Bmat * entrywisePolynomialDerivative Tmat)) := by
    rw [hentrywise]
    rw [← m.mapMatrix.map_mul]
    exact (AddMonoidHom.map_trace m.toAddMonoidHom
      (Bmat * entrywisePolynomialDerivative Tmat)).symm
  have hcoordinate :
      functionFieldDifferentialCoordinate (k := k) (F := F)
          ((algebraMap (B k F) F b) •
            differential k F (algebraMap (B k F) F t)) =
        algebraMap (B k F) F b * D (algebraMap (B k F) F t) := by
    rw [map_smul,
      functionFieldDifferentialCoordinate_differential]
    simp only [smul_eq_mul, D]
  rw [functionFieldDifferentialTrace_apply, hcoordinate, htrace, hBF, hTF,
    hmatrix]
  rfl
end QEC.Coding.AlgebraicGeometry.DirectIntegralDifferentialTraceRegularity
