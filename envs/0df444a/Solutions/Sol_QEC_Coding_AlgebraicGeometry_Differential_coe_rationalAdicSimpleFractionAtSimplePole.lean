-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicSimpleFractionAtSimplePole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:37:41.248923+00:00
-- url     : https://prove2.me/submissions/dd62711c-d7d5-47e5-a97b-dc38a8dd1e1b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_EulerTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSimpleFractionResidue
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
namespace Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
private theorem coe_rationalAdicRegularQuotient
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    ((rationalAdicRegularQuotient p b :
      (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k) =
      algebraMap k[X] (RatFunc k) b /
        algebraMap k[X] (RatFunc k)
          (GlobalPlace.rationalAdicPolynomial p).derivative := by
  unfold rationalAdicRegularQuotient
  rw [show
      (((GlobalPlace.rationalAdicPolynomialToValuationRing p b *
        ↑((rationalAdicPolynomialDerivative_isUnit p).unit⁻¹) :
          (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k)) =
        ((GlobalPlace.rationalAdicPolynomialToValuationRing p b :
          (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k) *
          (((↑((rationalAdicPolynomialDerivative_isUnit p).unit⁻¹) :
            (GlobalPlace.rationalAdic p).valuationRing)) : RatFunc k) by rfl]
  rw [GlobalPlace.coe_rationalAdicPolynomialToValuationRing]
  change algebraMap k[X] (RatFunc k) b *
      algebraMap (GlobalPlace.rationalAdic p).valuationRing (RatFunc k)
        (↑((rationalAdicPolynomialDerivative_isUnit p).unit⁻¹) :
          (GlobalPlace.rationalAdic p).valuationRing) = _
  rw [map_units_inv (algebraMap
      (GlobalPlace.rationalAdic p).valuationRing (RatFunc k))
      (rationalAdicPolynomialDerivative_isUnit p).unit,
    (rationalAdicPolynomialDerivative_isUnit p).unit_spec]
  change algebraMap k[X] (RatFunc k) b *
      (((GlobalPlace.rationalAdicPolynomialToValuationRing p
        (GlobalPlace.rationalAdicPolynomial p).derivative :
          (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k))⁻¹ = _
  rw [GlobalPlace.coe_rationalAdicPolynomialToValuationRing]
  rw [div_eq_mul_inv]
omit [Finite k] in
private theorem functionFieldDerivation_apply_polynomial (b : k[X]) :
    functionFieldDerivation (k := k) (F := RatFunc k)
        (algebraMap k[X] (RatFunc k) b) =
      algebraMap k[X] (RatFunc k) b.derivative := by
  have hX : functionFieldDerivation (k := k) (F := RatFunc k) RatFunc.X = 1 := by
    simpa using
      (functionFieldDerivation_apply_X (k := k) (F := RatFunc k))
  calc
    functionFieldDerivation (k := k) (F := RatFunc k)
        (algebraMap k[X] (RatFunc k) b) =
        functionFieldDerivation (k := k) (F := RatFunc k)
          (Polynomial.aeval RatFunc.X b) := by
            rw [RatFunc.aeval_X_left_eq_algebraMap]
    _ = Polynomial.aeval RatFunc.X b.derivative •
          functionFieldDerivation (k := k) (F := RatFunc k) RatFunc.X := by
            rw [Derivation.map_aeval]
    _ = Polynomial.aeval RatFunc.X b.derivative := by
          rw [hX, smul_eq_mul, mul_one]
    _ = algebraMap k[X] (RatFunc k) b.derivative :=
      RatFunc.aeval_X_left_eq_algebraMap b.derivative
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
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    ((rationalAdicSimpleFractionAtSimplePole p b :
      simplePoleDifferentialLattice (GlobalPlace.rationalAdic p)) :
        Differential k (RatFunc k)) =
      (algebraMap k[X] (RatFunc k) b /
        algebraMap k[X] (RatFunc k) (GlobalPlace.rationalAdicPolynomial p)) •
          functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
  change (rationalAdicRegularQuotient p b : RatFunc k) •
      logarithmicDifferential (k := k) (F := RatFunc k)
        (algebraMap k[X] (RatFunc k) (GlobalPlace.rationalAdicPolynomial p)) = _
  rw [coe_rationalAdicRegularQuotient, logarithmicDifferential,
    differential_eq_functionFieldDerivation_smul_generator,
    functionFieldDerivation_apply_polynomial]
  simp only [smul_smul]
  field_simp [rationalAdicPolynomial_map_ne_zero p,
    rationalAdicPolynomial_derivative_ne_zero p]
end QEC.Coding.AlgebraicGeometry.Differential
