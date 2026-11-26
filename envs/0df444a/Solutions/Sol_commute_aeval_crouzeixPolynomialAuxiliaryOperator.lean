-- Prove2me | solution 1 for commute_aeval_crouzeixPolynomialAuxiliaryOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:32:01.088247+00:00
-- url     : https://prove2.me/submissions/3cbdeee4-58e5-4346-a3cc-2bc851830a37

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Theorems.Thm_commute_aeval_resolvent
import Theorems.Thm_SmoothJordanDomain_boundaryParam_mem_resolventSet
import Theorems.Thm_contourIntegral_const_mul
import Theorems.Thm_contourIntegral_mul_const
import Theorems.Thm_crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable


set_option autoImplicit false
open Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
theorem _root_.solution
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (p q : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    Commute (Polynomial.aeval A p)
      (crouzeixPolynomialAuxiliaryOperator A Omega q) := by
  rw [Commute]
  change Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega q =
    crouzeixPolynomialAuxiliaryOperator A Omega q * Polynomial.aeval A p
  unfold crouzeixPolynomialAuxiliaryOperator crouzeixAuxiliaryOperator
  rw [mul_smul_comm, smul_mul_assoc]
  rw [← contourIntegral_const_mul (Polynomial.aeval A p)
    (crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable A Omega q hOmega)]
  rw [← contourIntegral_mul_const (Polynomial.aeval A p)
    (crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable A Omega q hOmega)]
  congr 1
  unfold contourIntegral
  apply intervalIntegral.integral_congr
  intro t _
  apply congrArg (fun Q : H →L[ℂ] H => deriv Omega.boundaryParam t • Q)
  change Polynomial.aeval A p *
      (star (Polynomial.eval (Omega.boundaryParam t) q) •
        resolvent A (Omega.boundaryParam t)) =
    (star (Polynomial.eval (Omega.boundaryParam t) q) •
        resolvent A (Omega.boundaryParam t)) * Polynomial.aeval A p
  rw [mul_smul_comm, smul_mul_assoc]
  apply congrArg (fun Q : H →L[ℂ] H =>
    star (Polynomial.eval (Omega.boundaryParam t) q) • Q)
  exact (commute_aeval_resolvent A p
    (Omega.boundaryParam_mem_resolventSet A hOmega t)).eq
