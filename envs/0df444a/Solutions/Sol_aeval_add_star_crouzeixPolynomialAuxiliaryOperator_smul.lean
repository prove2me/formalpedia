-- Prove2me | solution 1 for aeval_add_star_crouzeixPolynomialAuxiliaryOperator_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:24.059942+00:00
-- url     : https://prove2.me/submissions/6873095b-e709-4bdc-9a7d-69a6027f852c

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_smul
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
theorem _root_.solution
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) :
    Polynomial.aeval A (a • p) +
        star (crouzeixPolynomialAuxiliaryOperator A Omega (a • p)) =
      a • (Polynomial.aeval A p +
        star (crouzeixPolynomialAuxiliaryOperator A Omega p)) := by
  rw [crouzeixPolynomialAuxiliaryOperator_smul]
  simp only [map_smul, star_smul, star_star, smul_add]
