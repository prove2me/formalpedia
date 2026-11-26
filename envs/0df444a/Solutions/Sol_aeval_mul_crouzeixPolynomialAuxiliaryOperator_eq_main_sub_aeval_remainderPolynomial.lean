-- Prove2me | solution 1 for aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_aeval_remainderPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:38.932882+00:00
-- url     : https://prove2.me/submissions/c92dc792-20b6-4e00-9983-dc610af17feb

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
import Theorems.Thm_normalized_crouzeixProductRemainderContour_eq_aeval
import Theorems.Thm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_remainder

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
        Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) := by
  rw [aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_remainder
    A Omega p hOmega]
  rw [normalized_crouzeixProductRemainderContour_eq_aeval]
