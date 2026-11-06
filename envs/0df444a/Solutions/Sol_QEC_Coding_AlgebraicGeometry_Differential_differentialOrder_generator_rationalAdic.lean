-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.differentialOrder_generator_rationalAdic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:42:32.063451+00:00
-- url     : https://prove2.me/submissions/4bacf081-0ba5-4110-b49b-af93f37ecd86

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSimpleFractionResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinitySimpleFractionResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_differentialOrder_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_logarithmicDifferential_isGlobalSimplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_mem_localDifferentialLattice_iff_differentialOrder_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_logarithmicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differential_eq_functionFieldDerivation_smul_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicPolynomial_irreducible
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
private theorem ratFuncDifferentialOrder_rationalAdicPolynomial_derivative_ne_zero
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    (GlobalPlace.rationalAdicPolynomial p).derivative ≠ 0 := by
  exact (Polynomial.separable_iff_derivative_ne_zero
    (GlobalPlace.rationalAdicPolynomial_irreducible p)).mp
      (PerfectField.separable_of_irreducible
        (GlobalPlace.rationalAdicPolynomial_irreducible p))
private theorem ratFuncDifferentialOrder_rationalAdicPolynomial_derivative_not_mem
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    (GlobalPlace.rationalAdicPolynomial p).derivative ∉ p.asIdeal := by
  rw [GlobalPlace.rationalAdic_asIdeal_eq_span p,
    Ideal.mem_span_singleton, Polynomial.dvd_derivative_iff]
  exact ratFuncDifferentialOrder_rationalAdicPolynomial_derivative_ne_zero p
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
private theorem rationalAdic_order_polynomial
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    (GlobalPlace.rationalAdic p).order
        (algebraMap k[X] (RatFunc k)
          (GlobalPlace.rationalAdicPolynomial p)) = 1 := by
  unfold GlobalPlace.order GlobalPlace.rationalAdic
  rw [p.valuation_of_algebraMap,
    p.intValuation_singleton
      (GlobalPlace.rationalAdicPolynomial_irreducible p).ne_zero
      (GlobalPlace.rationalAdic_asIdeal_eq_span p)]
  simp
private theorem rationalAdic_order_derivative
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    (GlobalPlace.rationalAdic p).order
        (algebraMap k[X] (RatFunc k)
          (GlobalPlace.rationalAdicPolynomial p).derivative) = 0 := by
  have hvaluation :
      (GlobalPlace.rationalAdic p).valuation
          (algebraMap k[X] (RatFunc k)
            (GlobalPlace.rationalAdicPolynomial p).derivative) = 1 := by
    change (p.valuation (RatFunc k))
        (algebraMap k[X] (RatFunc k)
          (GlobalPlace.rationalAdicPolynomial p).derivative) = 1
    exact (p.valuation_eq_one_iff_notMem (K := RatFunc k)).mpr
      (ratFuncDifferentialOrder_rationalAdicPolynomial_derivative_not_mem p)
  unfold GlobalPlace.order
  rw [hvaluation]
  simp
private theorem differentialOrder_logarithmic_eq_neg_one_of_order_eq_one
    (P : GlobalPlace k (RatFunc k)) (f : RatFunc k) (hf : f ≠ 0)
    (horder : P.order f = 1) :
    differentialOrder (k := k) (F := RatFunc k) P
        (logarithmicDifferential (k := k) (F := RatFunc k) f)
        (logarithmicDifferential_ne_zero_of_order_eq_one P f hf horder) = -1 := by
  let omega := logarithmicDifferential (k := k) (F := RatFunc k) f
  let homega : omega ≠ 0 :=
    logarithmicDifferential_ne_zero_of_order_eq_one P f hf horder
  have hsimple : omega ∈ simplePoleDifferentialLattice P :=
    logarithmicDifferential_isGlobalSimplePole
      (k := k) (F := RatFunc k) f hf P
  have hresidue :
      simplePoleResidue (k := k) (F := RatFunc k) P
          (logarithmicDifferentialAtSimplePole
            (k := k) (F := RatFunc k) P f hf) = 1 := by
    simpa only [horder, Int.cast_one] using
      (simplePoleResidue_logarithmicDifferential
        (k := k) (F := RatFunc k) P f hf)
  have hnotRegular : omega ∉ localDifferentialLattice P := by
    intro hregular
    have hzero := simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
      (k := k) (F := RatFunc k) P
      (logarithmicDifferentialAtSimplePole
        (k := k) (F := RatFunc k) P f hf) hregular
    rw [hresidue] at hzero
    exact one_ne_zero hzero
  have hge : -1 ≤ differentialOrder (k := k) (F := RatFunc k) P omega homega :=
    (mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
      (k := k) (F := RatFunc k) P omega homega).mp hsimple
  have hnge : ¬ 0 ≤ differentialOrder (k := k) (F := RatFunc k) P omega homega := by
    intro hnonnegative
    apply hnotRegular
    exact (mem_localDifferentialLattice_iff_differentialOrder_nonnegative
      (k := k) (F := RatFunc k) P omega homega).mpr hnonnegative
  apply le_antisymm
  · exact Int.le_sub_one_iff.mpr (lt_of_not_ge hnge)
  · exact hge
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
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    differentialOrder (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k)) = 0 := by
  let q : RatFunc k := algebraMap k[X] (RatFunc k)
    (GlobalPlace.rationalAdicPolynomial p)
  let q' : RatFunc k := algebraMap k[X] (RatFunc k)
    (GlobalPlace.rationalAdicPolynomial p).derivative
  let c : RatFunc k := q⁻¹ * q'
  have hq : q ≠ 0 := RatFunc.algebraMap_ne_zero
    (GlobalPlace.rationalAdicPolynomial_irreducible p).ne_zero
  have hq' : q' ≠ 0 := RatFunc.algebraMap_ne_zero
    (ratFuncDifferentialOrder_rationalAdicPolynomial_derivative_ne_zero p)
  have hc : c ≠ 0 := mul_ne_zero (inv_ne_zero hq) hq'
  have hqOrder : (GlobalPlace.rationalAdic p).order q = 1 :=
    rationalAdic_order_polynomial p
  have hq'Order : (GlobalPlace.rationalAdic p).order q' = 0 :=
    rationalAdic_order_derivative p
  have hcOrder : (GlobalPlace.rationalAdic p).order c = -1 := by
    dsimp only [c]
    rw [GlobalPlace.order_mul (GlobalPlace.rationalAdic p)
      (inv_ne_zero hq) hq', GlobalPlace.order_inv, hqOrder, hq'Order]
    omega
  have hlogEq : logarithmicDifferential (k := k) (F := RatFunc k) q =
      c • functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
    rw [logarithmicDifferential,
      differential_eq_functionFieldDerivation_smul_generator,
      show functionFieldDerivation (k := k) (F := RatFunc k) q = q' by
        exact functionFieldDerivation_apply_polynomial
          (GlobalPlace.rationalAdicPolynomial p)]
    simp only [smul_smul, smul_eq_mul, c]
  have hlogOrder := differentialOrder_logarithmic_eq_neg_one_of_order_eq_one
    (GlobalPlace.rationalAdic p) q hq hqOrder
  have hscaledOrder :
      differentialOrder (k := k) (F := RatFunc k)
          (GlobalPlace.rationalAdic p)
          (c • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
          (smul_ne_zero hc
            (functionFieldDifferentialGenerator_ne_zero
              (k := k) (F := RatFunc k))) = -1 := by
    simpa only [hlogEq] using hlogOrder
  rw [differentialOrder_smul (k := k) (F := RatFunc k)
    (GlobalPlace.rationalAdic p) c hc
    (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
    (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k)),
    hcOrder] at hscaledOrder
  omega
end QEC.Coding.AlgebraicGeometry.Differential
