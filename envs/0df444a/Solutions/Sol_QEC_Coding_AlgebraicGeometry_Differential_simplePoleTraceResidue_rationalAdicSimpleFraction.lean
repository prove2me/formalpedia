-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue_rationalAdicSimpleFraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:45:55.064342+00:00
-- url     : https://prove2.me/submissions/40a2a026-5888-4604-aa0a-034475d3b1cd

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_EulerTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSimpleFractionResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_logarithmicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicPolynomial_irreducible
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicPolynomial_monic
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncEulerTrace_trace_aeval_div_derivative
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
private theorem rationalAdicResidue_regularQuotient
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X])
    [Fact (Irreducible (GlobalPlace.rationalAdicPolynomial p))] :
    (GlobalPlace.rationalAdic p).residue (rationalAdicRegularQuotient p b) =
      GlobalPlace.rationalAdicResidueEquiv p
        (Polynomial.aeval
            (AdjoinRoot.root (GlobalPlace.rationalAdicPolynomial p)) b /
          Polynomial.aeval
            (AdjoinRoot.root (GlobalPlace.rationalAdicPolynomial p))
            (GlobalPlace.rationalAdicPolynomial p).derivative) := by
  calc
    (GlobalPlace.rationalAdic p).residue (rationalAdicRegularQuotient p b) =
        (GlobalPlace.rationalAdic p).residue
            (GlobalPlace.rationalAdicPolynomialToValuationRing p b) *
          ((GlobalPlace.rationalAdic p).residue
            (GlobalPlace.rationalAdicPolynomialToValuationRing p
              (GlobalPlace.rationalAdicPolynomial p).derivative))⁻¹ := by
      unfold rationalAdicRegularQuotient
      rw [map_mul, map_units_inv,
        (rationalAdicPolynomialDerivative_isUnit p).unit_spec]
    _ = GlobalPlace.rationalAdicResidueEquiv p
          (AdjoinRoot.mk (GlobalPlace.rationalAdicPolynomial p) b) *
        (GlobalPlace.rationalAdicResidueEquiv p
          (AdjoinRoot.mk (GlobalPlace.rationalAdicPolynomial p)
            (GlobalPlace.rationalAdicPolynomial p).derivative))⁻¹ := by
      rw [GlobalPlace.rationalAdicResidueEquiv_mk,
        GlobalPlace.rationalAdicResidueEquiv_mk]
    _ = GlobalPlace.rationalAdicResidueEquiv p
        (Polynomial.aeval
            (AdjoinRoot.root (GlobalPlace.rationalAdicPolynomial p)) b /
          Polynomial.aeval
            (AdjoinRoot.root (GlobalPlace.rationalAdicPolynomial p))
            (GlobalPlace.rationalAdicPolynomial p).derivative) := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.aeval_eq, map_div₀]
      rw [div_eq_mul_inv]
private theorem simplePoleResidue_rationalAdicSimpleFraction
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X])
    [Fact (Irreducible (GlobalPlace.rationalAdicPolynomial p))] :
    simplePoleResidue (k := k) (F := RatFunc k) (GlobalPlace.rationalAdic p)
        (rationalAdicSimpleFractionAtSimplePole p b) =
      GlobalPlace.rationalAdicResidueEquiv p
        (Polynomial.aeval
            (AdjoinRoot.root (GlobalPlace.rationalAdicPolynomial p)) b /
          Polynomial.aeval
            (AdjoinRoot.root (GlobalPlace.rationalAdicPolynomial p))
            (GlobalPlace.rationalAdicPolynomial p).derivative) := by
  unfold rationalAdicSimpleFractionAtSimplePole
  rw [simplePoleResidue_smul,
    simplePoleResidue_logarithmicDifferential,
    rationalAdic_order_polynomial]
  simp only [Int.cast_one, mul_one]
  exact rationalAdicResidue_regularQuotient p b
private theorem rationalAdicResidueEquiv_algebraMap
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (a : k) :
    letI : Algebra k (GlobalPlace.rationalAdic p).residueField :=
      GlobalPlace.residueAlgebra (GlobalPlace.rationalAdic p)
    GlobalPlace.rationalAdicResidueEquiv p
        (algebraMap k (AdjoinRoot (GlobalPlace.rationalAdicPolynomial p)) a) =
      algebraMap k (GlobalPlace.rationalAdic p).residueField a := by
  letI : Algebra k (GlobalPlace.rationalAdic p).residueField :=
    GlobalPlace.residueAlgebra (GlobalPlace.rationalAdic p)
  change (GlobalPlace.rationalAdic p).residue
      (GlobalPlace.rationalAdicPolynomialToValuationRing p (Polynomial.C a)) =
    (GlobalPlace.rationalAdic p).residue
      (GlobalPlace.constantsToValuationRing (GlobalPlace.rationalAdic p) a)
  apply congrArg (GlobalPlace.rationalAdic p).residue
  apply Subtype.ext
  simp only [GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
    GlobalPlace.coe_constantsToValuationRing, RatFunc.algebraMap_C,
    RatFunc.algebraMap_eq_C]
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
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X])
    (hb : b.degree < (GlobalPlace.rationalAdicPolynomial p).degree) :
    simplePoleTraceResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (rationalAdicSimpleFractionAtSimplePole p b :
          Differential k (RatFunc k))
        (rationalAdicSimpleFractionAtSimplePole p b).property =
      b.coeff ((GlobalPlace.rationalAdicPolynomial p).natDegree - 1) := by
  letI : Fact (Irreducible (GlobalPlace.rationalAdicPolynomial p)) :=
    ⟨GlobalPlace.rationalAdicPolynomial_irreducible p⟩
  letI : Algebra k (GlobalPlace.rationalAdic p).residueField :=
    GlobalPlace.residueAlgebra (GlobalPlace.rationalAdic p)
  letI : FiniteDimensional k (GlobalPlace.rationalAdic p).residueField :=
    GlobalPlace.residueField_finiteDimensional (GlobalPlace.rationalAdic p)
  let e := GlobalPlace.rationalAdicResidueEquiv p
  have he : RingHom.comp
      (algebraMap k (GlobalPlace.rationalAdic p).residueField)
      (RingEquiv.refl k) =
      RingHom.comp (e : AdjoinRoot (GlobalPlace.rationalAdicPolynomial p) →+*
        (GlobalPlace.rationalAdic p).residueField)
        (algebraMap k (AdjoinRoot (GlobalPlace.rationalAdicPolynomial p))) := by
    ext a
    simp only [RingHom.comp_apply, e]
    exact (rationalAdicResidueEquiv_algebraMap p a).symm
  let x : AdjoinRoot (GlobalPlace.rationalAdicPolynomial p) :=
    Polynomial.aeval
        (AdjoinRoot.root (GlobalPlace.rationalAdicPolynomial p)) b /
      Polynomial.aeval
        (AdjoinRoot.root (GlobalPlace.rationalAdicPolynomial p))
        (GlobalPlace.rationalAdicPolynomial p).derivative
  change Algebra.trace k (GlobalPlace.rationalAdic p).residueField
      (simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (rationalAdicSimpleFractionAtSimplePole p b)) = _
  rw [simplePoleResidue_rationalAdicSimpleFraction]
  calc
    Algebra.trace k (GlobalPlace.rationalAdic p).residueField (e x) =
        Algebra.trace k (AdjoinRoot (GlobalPlace.rationalAdicPolynomial p)) x := by
      exact (Algebra.trace_eq_of_equiv_equiv (RingEquiv.refl k) e he x).symm
    _ = b.coeff ((GlobalPlace.rationalAdicPolynomial p).natDegree - 1) :=
      RatFuncEulerTrace.trace_aeval_div_derivative
        (GlobalPlace.rationalAdicPolynomial p) b
        (GlobalPlace.rationalAdicPolynomial_monic p) hb
end QEC.Coding.AlgebraicGeometry.Differential
