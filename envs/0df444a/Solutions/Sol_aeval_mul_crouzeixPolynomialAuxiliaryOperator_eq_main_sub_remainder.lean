-- Prove2me | solution 1 for aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_remainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:33:36.102531+00:00
-- url     : https://prove2.me/submissions/0f78b1a6-3835-4cf1-b241-7dc0e53424f5

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
import Theorems.Thm_crouzeixProductMainIntegrand_contourIntegrable
import Theorems.Thm_crouzeixProductRemainderIntegrand_contourIntegrable
import Theorems.Thm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_split
import Theorems.Thm_contourIntegral_sub


set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
          contourIntegral
            (fun z => (star (Polynomial.eval z p) * Polynomial.eval z p) •
              resolvent A z) Omega.boundaryParam -
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
          contourIntegral
            (fun z => star (Polynomial.eval z p) •
              Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
            Omega.boundaryParam := by
  rw [aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_split A Omega p hOmega]
  rw [contourIntegral_sub
    (crouzeixProductMainIntegrand_contourIntegrable A Omega p hOmega)
    (crouzeixProductRemainderIntegrand_contourIntegrable A Omega p)]
  rw [smul_sub]
