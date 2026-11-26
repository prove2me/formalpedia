-- Prove2me | solution 1 for aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:59.124229+00:00
-- url     : https://prove2.me/submissions/0d285fef-a6ae-4066-aea3-9ffdc43efad1

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Theorems.Thm_aeval_mul_smul_resolvent_eq_smul_eval_mul_resolvent_sub_aeval_divByMonic
import Theorems.Thm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_contourIntegral
import Theorems.Thm_SmoothJordanDomain_boundaryParam_mem_resolventSet


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
          (fun z =>
            (star (Polynomial.eval z p) * Polynomial.eval z p) • resolvent A z -
              star (Polynomial.eval z p) •
                Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
          Omega.boundaryParam := by
  rw [aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_contourIntegral A Omega p hOmega]
  congr 1
  unfold contourIntegral
  apply intervalIntegral.integral_congr
  intro t _
  apply congrArg (fun Q : H →L[ℂ] H => deriv Omega.boundaryParam t • Q)
  exact aeval_mul_smul_resolvent_eq_smul_eval_mul_resolvent_sub_aeval_divByMonic
    A p (Omega.boundaryParam_mem_resolventSet A hOmega t)
      (star (Polynomial.eval (Omega.boundaryParam t) p))
