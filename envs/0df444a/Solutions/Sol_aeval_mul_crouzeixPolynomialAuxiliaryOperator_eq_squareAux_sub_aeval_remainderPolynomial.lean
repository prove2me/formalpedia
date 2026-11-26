-- Prove2me | solution 1 for aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_squareAux_sub_aeval_remainderPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:35:28.795268+00:00
-- url     : https://prove2.me/submissions/474a5c42-8608-4109-822d-85f92914abf2

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
import Theorems.Thm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_aeval_remainderPolynomial

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
      crouzeixAuxiliaryOperator A Omega
          (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) -
        Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) := by
  rw [
    aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_main_sub_aeval_remainderPolynomial
      A Omega p hOmega]
  rfl
