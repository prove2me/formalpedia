-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalClearedMonomial_taylor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:23:16.867072+00:00
-- url     : https://prove2.me/submissions/3b62faa3-4eca-4381-9c3c-137d82421c79

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_qpow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQSeries_dilated_map
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPower_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQCoefficient_analytic_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQSeries_map
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : N≠0) (B i k : ℕ) :
    lpsOriginalTaylorSeries (lpsOriginalClearedMonomial N B i k)=
      PowerSeries.map (algebraMap ℚ ℂ) (lpsOriginalClearedFormalMonomial N hN B i k) := by
  have hKN : AnalyticAt ℂ (fun q : ℂ=>lpsOriginalJQCoefficient (q^N)) 0 := by
    exact lpsOriginalJQCoefficient_analytic_zero.comp_of_eq
      (lpsOriginalPower_analytic N) (zero_pow hN)
  change lpsOriginalTaylorSeries
    (((fun q : ℂ=>q^(B-(i+N*k)))*(lpsOriginalJQCoefficient^i))*
      ((fun q : ℂ=>lpsOriginalJQCoefficient (q^N))^k))=_
  rw [lpsOriginalTaylorSeries_mul
    ((lpsOriginalPower_analytic _).mul (lpsOriginalJQCoefficient_analytic_zero.pow i)) (hKN.pow k),
    lpsOriginalTaylorSeries_mul (lpsOriginalPower_analytic _) (lpsOriginalJQCoefficient_analytic_zero.pow i),
    lpsOriginalTaylorSeries_qpow,
    lpsOriginalTaylorSeries_pow lpsOriginalJQCoefficient_analytic_zero,
    lpsOriginalTaylorSeries_pow hKN]
  simp only [lpsOriginalClearedFormalMonomial,map_mul,map_pow,PowerSeries.map_X,
    lpsOriginalJQSeries_map,lpsOriginalJQSeries_dilated_map]
end QEC.Coding.TannerLiftedProduct
