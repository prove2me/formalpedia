-- Prove2me | solution 1 for aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_contourIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:13.062211+00:00
-- url     : https://prove2.me/submissions/0cb4afb9-ada6-44f3-8878-49c3a31883e8

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Theorems.Thm_contourIntegral_const_mul
import Theorems.Thm_crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable


set_option autoImplicit false
open Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
theorem _root_.solution
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        contourIntegral
          (fun z => Polynomial.aeval A p *
            (star (Polynomial.eval z p) • resolvent A z))
          Omega.boundaryParam := by
  unfold crouzeixPolynomialAuxiliaryOperator crouzeixAuxiliaryOperator
  rw [mul_smul_comm]
  rw [← contourIntegral_const_mul (Polynomial.aeval A p)
    (crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable A Omega p hOmega)]
