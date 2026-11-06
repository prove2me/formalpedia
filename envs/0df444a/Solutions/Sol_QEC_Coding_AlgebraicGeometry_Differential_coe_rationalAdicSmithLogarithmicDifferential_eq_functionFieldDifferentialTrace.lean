-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicSmithLogarithmicDifferential_eq_functionFieldDifferentialTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:49:56.93158+00:00
-- url     : https://prove2.me/submissions/55c2a302-b04e-4430-a00f-64bc5d711630

import Mathlib.RingTheory.Localization.NormTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSmithMatrixResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SmithDifferentialTrace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicSmithLogarithmicDifferentialAtSimplePole
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
namespace QEC.Coding.AlgebraicGeometry
namespace Differential
variable {k F : Type*} [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] smithDifferentialTrace_constantAlgebra
attribute [local instance] smithDifferentialTrace_scalarTower
private theorem functionFieldDerivation_extends_rationalDerivation
    (c : RatFunc k) :
    FunctionFieldDifferential.functionFieldDerivation (k := k) (F := F)
        (algebraMap (RatFunc k) F c) =
      algebraMap (RatFunc k) F
        (RatFuncDerivation.rationalDerivation
          (k := k) (M := RatFunc k) 1 c) := by
  let D₀ := RatFuncDerivation.rationalDerivation
    (k := k) (M := RatFunc k) 1
  rw [FunctionFieldDifferential.functionFieldDerivation,
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
private theorem rationalDiagonalMatrixInverse_mul_map_diagonal
    {n : Type*} [Fintype n] [DecidableEq n]
    (a : n → k[X]) (ha : ∀ i, a i ≠ 0) :
    rationalDiagonalMatrixInverse a *
        (algebraMap k[X] (RatFunc k)).mapMatrix (Matrix.diagonal a) = 1 := by
  classical
  unfold rationalDiagonalMatrixInverse
  simp only [RingHom.mapMatrix_apply]
  rw [Matrix.diagonal_map (map_zero (algebraMap k[X] (RatFunc k))),
    Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    have hai : algebraMap k[X] (RatFunc k) (a i) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (ha i)
    simp [Matrix.one_apply, hai]
  · simp [Matrix.one_apply, hij]
private theorem smith_target_matrix_eq_diagonal_mul_change
    {n : ℕ}
    (source target : Module.Basis (Fin n) k[X] (B (k := k) (F := F)))
    (a : Fin n → k[X])
    (t : B (k := k) (F := F))
    (hdiag : LinearMap.toMatrix source target
      (Algebra.lmul k[X] (B (k := k) (F := F)) t) = Matrix.diagonal a) :
    LinearMap.toMatrix target target
        (Algebra.lmul k[X] (B (k := k) (F := F)) t) =
      Matrix.diagonal a * source.toMatrix target := by
  rw [← hdiag]
  symm
  exact linearMap_toMatrix_mul_basis_toMatrix target source target
    (Algebra.lmul k[X] (B (k := k) (F := F)) t)
end Differential
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open scoped Polynomial RatFunc nonZeroDivisors
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
variable {k F : Type*} [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.Differential.smithDifferentialTrace_constantAlgebra
attribute [local instance] smithDifferentialTrace_constantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.Differential.smithDifferentialTrace_scalarTower
attribute [local instance] smithDifferentialTrace_scalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.Differential._p2m_local_instance_4de610a81f_51
attribute [local instance] QEC.Coding.AlgebraicGeometry.Differential._p2m_local_instance_4de610a81f_55
attribute [local instance] QEC.Coding.AlgebraicGeometry.Differential._p2m_local_instance_4de610a81f_58
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    {n : ℕ}
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (source target : Module.Basis (Fin n) k[X]
      (_root_.FunctionField.ringOfIntegers k F))
    (a : Fin n → k[X]) (ha : ∀ i, a i ≠ 0)
    (t b : _root_.FunctionField.ringOfIntegers k F) (ht : t ≠ 0)
    (hdiag : LinearMap.toMatrix source target
      (Algebra.lmul k[X]
        (_root_.FunctionField.ringOfIntegers k F) t) = Matrix.diagonal a) :
    ((rationalAdicSmithLogarithmicDifferentialAtSimplePole p
        source target a ha
        (Algebra.lmul k[X]
          (_root_.FunctionField.ringOfIntegers k F) b) :
          simplePoleDifferentialLattice (GlobalPlace.rationalAdic p)) :
        Differential k (RatFunc k)) =
      FunctionFieldDifferential.functionFieldDifferentialTrace
        (k := k) (F := F)
        ((algebraMap (_root_.FunctionField.ringOfIntegers k F) F b) •
          logarithmicDifferential (k := k) (F := F)
            (algebraMap (_root_.FunctionField.ringOfIntegers k F) F t)) := by
  classical
  let m := algebraMap k[X] (RatFunc k)
  let D₀ := RatFuncDerivation.rationalDerivation
    (k := k) (M := RatFunc k) 1
  let D := FunctionFieldDifferential.functionFieldDerivation (k := k) (F := F)
  let targetF := target.localizationLocalization
    (RatFunc k) k[X]⁰ F
  let T : Matrix (Fin n) (Fin n) (RatFunc k) :=
    m.mapMatrix (LinearMap.toMatrix target target
      (Algebra.lmul k[X] (B (k := k) (F := F)) t))
  let G : Matrix (Fin n) (Fin n) (RatFunc k) :=
    m.mapMatrix (LinearMap.toMatrix target target
      (Algebra.lmul k[X] (B (k := k) (F := F)) b))
  let P : Matrix (Fin n) (Fin n) (RatFunc k) :=
    m.mapMatrix (target.toMatrix source)
  let Q : Matrix (Fin n) (Fin n) (RatFunc k) :=
    m.mapMatrix (source.toMatrix target)
  let A : Matrix (Fin n) (Fin n) (RatFunc k) :=
    m.mapMatrix (Matrix.diagonal a)
  let Ainv : Matrix (Fin n) (Fin n) (RatFunc k) :=
    rationalDiagonalMatrixInverse a
  let TF : Matrix (Fin n) (Fin n) (RatFunc k) :=
    LinearMap.toMatrix targetF targetF
      (Algebra.lmul (RatFunc k) F
        (algebraMap (B (k := k) (F := F)) F t))
  let UF : Matrix (Fin n) (Fin n) (RatFunc k) :=
    LinearMap.toMatrix targetF targetF
      (Algebra.lmul (RatFunc k) F
        (algebraMap (B (k := k) (F := F)) F t)⁻¹)
  have htF_ne : algebraMap (B (k := k) (F := F)) F t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective
      (B (k := k) (F := F)) F)).mpr ht
  have hTF : TF = T := by
    symm
    exact Algebra.map_leftMulMatrix_localization
      (Rₘ := RatFunc k) (Sₘ := F) k[X] k[X]⁰ target t
  have hGF :
      LinearMap.toMatrix targetF targetF
          (Algebra.lmul (RatFunc k) F
            (algebraMap (B (k := k) (F := F)) F b)) = G := by
    symm
    exact Algebra.map_leftMulMatrix_localization
      (Rₘ := RatFunc k) (Sₘ := F) k[X] k[X]⁰ target b
  have hT : T = A * Q := by
    have h := congrArg m.mapMatrix
      (smith_target_matrix_eq_diagonal_mul_change source target a t hdiag)
    simpa only [T, A, Q, map_mul] using h
  have hAinvA : Ainv * A = 1 := by
    exact rationalDiagonalMatrixInverse_mul_map_diagonal a ha
  have hPQ : P * Q = 1 := by
    have h := congrArg m.mapMatrix
      (Module.Basis.toMatrix_mul_toMatrix_flip target source)
    simpa only [P, Q, map_mul, map_one] using h
  have hcandidateT : (P * Ainv) * T = 1 := by
    rw [hT]
    calc
      (P * Ainv) * (A * Q) = P * (Ainv * A) * Q := by
        simp only [Matrix.mul_assoc]
      _ = P * Q := by rw [hAinvA, mul_one]
      _ = 1 := hPQ
  have hTFUF : TF * UF = 1 := by
    dsimp only [TF, UF]
    rw [← LinearMap.toMatrix_mul, ← map_mul,
      mul_inv_cancel₀ htF_ne, map_one, LinearMap.toMatrix_one]
  have hcandidateUF : P * Ainv = UF := by
    calc
      P * Ainv = (P * Ainv) * 1 := by rw [mul_one]
      _ = (P * Ainv) * (TF * UF) := by rw [hTFUF]
      _ = ((P * Ainv) * TF) * UF := by
        simp only [Matrix.mul_assoc]
      _ = UF := by rw [hTF, hcandidateT, one_mul]
  have htrace :=
    FunctionFieldDifferential.derivation_logarithmic_trace_eq_matrix_trace
      D₀ D
      (functionFieldDerivation_extends_rationalDerivation
        (k := k) (F := F)) targetF
      (algebraMap (B (k := k) (F := F)) F b)
      (algebraMap (B (k := k) (F := F)) F t) htF_ne
  have hcoordinate :
      FunctionFieldDifferential.functionFieldDifferentialCoordinate
          (k := k) (F := F)
          ((algebraMap (B (k := k) (F := F)) F b) •
            logarithmicDifferential (k := k) (F := F)
              (algebraMap (B (k := k) (F := F)) F t)) =
        algebraMap (B (k := k) (F := F)) F b *
          D (algebraMap (B (k := k) (F := F)) F t) *
            (algebraMap (B (k := k) (F := F)) F t)⁻¹ := by
    rw [logarithmicDifferential, map_smul, map_smul,
      FunctionFieldDifferential.functionFieldDifferentialCoordinate_differential]
    simp only [smul_eq_mul, D]
    ring
  rw [coe_rationalAdicSmithLogarithmicDifferentialAtSimplePole
      (p := p) source target a ha
      (Algebra.lmul k[X] (B (k := k) (F := F)) t)
      (Algebra.lmul k[X] (B (k := k) (F := F)) b) hdiag,
    FunctionFieldDifferential.functionFieldDifferentialTrace_apply,
    hcoordinate, htrace]
  rw [hGF]
  change Matrix.trace
      (G * P * Ainv * entrywiseMatrixDerivation D₀ T) •
        FunctionFieldDifferential.functionFieldDifferentialGenerator
          (k := k) (F := RatFunc k) =
    Matrix.trace
      (G * UF * entrywiseMatrixDerivation D₀ TF) •
        FunctionFieldDifferential.functionFieldDifferentialGenerator
          (k := k) (F := RatFunc k)
  rw [show G * P * Ainv = G * (P * Ainv) from
      Matrix.mul_assoc G P Ainv,
    hcandidateUF, hTF]
end QEC.Coding.AlgebraicGeometry.Differential
