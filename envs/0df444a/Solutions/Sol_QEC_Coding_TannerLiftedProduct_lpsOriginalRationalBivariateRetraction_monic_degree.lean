-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRationalBivariateRetraction_monic_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:19:01.649564+00:00
-- url     : https://prove2.me/submissions/4135be34-96fe-408b-9c89-e7337f8cee29

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalPolynomialRetraction_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalPolynomialRetraction_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalBivariateRetraction_coeff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (P : Polynomial (Polynomial ℂ)) (hP : P.Monic) :
    (lpsOriginalRationalBivariateRetraction P).Monic ∧
      (lpsOriginalRationalBivariateRetraction P).natDegree=P.natDegree := by
  have hle : (lpsOriginalRationalBivariateRetraction P).natDegree≤P.natDegree := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [lpsOriginalRationalBivariateRetraction_coeff,
      Polynomial.coeff_eq_zero_of_natDegree_lt hn,lpsOriginalRationalPolynomialRetraction_zero]
  have hc : (lpsOriginalRationalBivariateRetraction P).coeff P.natDegree=1 := by
    rw [lpsOriginalRationalBivariateRetraction_coeff,hP.coeff_natDegree,
      lpsOriginalRationalPolynomialRetraction_one]
  have hd := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hc];exact one_ne_zero)
  refine ⟨?_,hd⟩
  change (lpsOriginalRationalBivariateRetraction P).coeff
    (lpsOriginalRationalBivariateRetraction P).natDegree=1
  rw [hd,hc]
end QEC.Coding.TannerLiftedProduct
