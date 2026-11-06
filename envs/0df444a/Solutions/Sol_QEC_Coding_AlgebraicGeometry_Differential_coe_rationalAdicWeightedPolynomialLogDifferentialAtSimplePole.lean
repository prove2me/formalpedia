-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicWeightedPolynomialLogDifferentialAtSimplePole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:39:41.192109+00:00
-- url     : https://prove2.me/submissions/0ce006f1-8e63-4243-aa50-aad04d99f123

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialLogarithmicResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differential_eq_functionFieldDerivation_smul_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
open scoped Polynomial RatFunc WithZero
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
variable {k : Type*} [Field k] [Finite k]
end GlobalPlace
namespace Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
omit [Finite k] in
private theorem functionFieldDerivation_apply_polynomial (a : k[X]) :
    functionFieldDerivation (k := k) (F := RatFunc k)
        (algebraMap k[X] (RatFunc k) a) =
      algebraMap k[X] (RatFunc k) a.derivative := by
  have hX :
      functionFieldDerivation (k := k) (F := RatFunc k) RatFunc.X = 1 := by
    simpa using
      (functionFieldDerivation_apply_X (k := k) (F := RatFunc k))
  calc
    functionFieldDerivation (k := k) (F := RatFunc k)
        (algebraMap k[X] (RatFunc k) a) =
        functionFieldDerivation (k := k) (F := RatFunc k)
          (Polynomial.aeval RatFunc.X a) := by
            rw [RatFunc.aeval_X_left_eq_algebraMap]
    _ = Polynomial.aeval RatFunc.X a.derivative •
          functionFieldDerivation (k := k) (F := RatFunc k) RatFunc.X := by
            rw [Derivation.map_aeval]
    _ = Polynomial.aeval RatFunc.X a.derivative := by
          rw [hX, smul_eq_mul, mul_one]
    _ = algebraMap k[X] (RatFunc k) a.derivative :=
      RatFunc.aeval_X_left_eq_algebraMap a.derivative
end Differential
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (r a : k[X]) (ha : a ≠ 0) :
    ((rationalAdicWeightedPolynomialLogDifferentialAtSimplePole p r a ha :
      simplePoleDifferentialLattice (GlobalPlace.rationalAdic p)) :
        Differential k (RatFunc k)) =
      (algebraMap k[X] (RatFunc k) r *
          (algebraMap k[X] (RatFunc k) a)⁻¹ *
          algebraMap k[X] (RatFunc k) a.derivative) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
  change
    ((GlobalPlace.rationalAdicPolynomialToValuationRing p r :
      (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k) •
        logarithmicDifferential (k := k) (F := RatFunc k)
          (algebraMap k[X] (RatFunc k) a) = _
  rw [GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
    logarithmicDifferential,
    differential_eq_functionFieldDerivation_smul_generator,
    functionFieldDerivation_apply_polynomial]
  simp only [smul_smul, smul_eq_mul]
  ring
end QEC.Coding.AlgebraicGeometry.Differential
