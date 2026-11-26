-- Prove2me | solution 1 for aeval_mul_crouzeixPolynomialAuxiliaryOperator_add_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:21:36.864626+00:00
-- url     : https://prove2.me/submissions/bf1890ad-da09-4ed3-9cf5-2e51bef90fde

import Definitions.Def_Operator_Crouzeix_ProductContour
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ProductBase
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_add_C
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ) (a : ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hCauchy : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * Complex.I) • (1 : E →L[ℂ] E)) :
    Polynomial.aeval A (p + Polynomial.C a) *
        crouzeixPolynomialAuxiliaryOperator A Omega (p + Polynomial.C a) =
      Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p +
        star a • Polynomial.aeval A p +
        a • crouzeixPolynomialAuxiliaryOperator A Omega p +
        (a * star a) • (1 : E →L[ℂ] E) := by
  rw [map_add, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
    crouzeixPolynomialAuxiliaryOperator_add_C A Omega p a hOmega hCauchy]
  simp only [add_mul, mul_add, mul_smul_comm, smul_mul_assoc,
    one_mul, mul_one]
  module
