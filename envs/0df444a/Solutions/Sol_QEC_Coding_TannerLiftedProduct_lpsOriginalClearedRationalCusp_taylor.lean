-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalClearedRationalCusp_taylor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:25:56.866629+00:00
-- url     : https://prove2.me/submissions/25b40332-5ae5-4fee-a02f-3640005d6c7b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_const_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_sum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedMonomial_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedMonomial_taylor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
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
theorem _root_.solution (N : ℕ) (hN : N≠0) (B : ℕ)
    (P : Polynomial (Polynomial ℂ)) :
    lpsOriginalTaylorSeries (lpsOriginalClearedRationalCusp N B P)=
      PowerSeries.map (algebraMap ℚ ℂ) (lpsOriginalClearedFormal N hN B P) := by
  classical
  unfold lpsOriginalClearedRationalCusp lpsOriginalClearedFormal
  simp only [map_sum,map_mul,PowerSeries.map_C]
  rw [lpsOriginalTaylorSeries_sum P.support (fun k=>∑ i∈(P.coeff k).support,fun q=>(lpsOriginalRationalRetraction ((P.coeff k).coeff i):ℂ)*lpsOriginalClearedMonomial N B i k q) (fun k _=>
    (P.coeff k).support.analyticAt_sum fun i _=>analyticAt_const.mul
      (lpsOriginalClearedMonomial_analytic N hN B i k))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [lpsOriginalTaylorSeries_sum (P.coeff k).support (fun i=>fun q=>(lpsOriginalRationalRetraction ((P.coeff k).coeff i):ℂ)*lpsOriginalClearedMonomial N B i k q) (fun i _=>analyticAt_const.mul
    (lpsOriginalClearedMonomial_analytic N hN B i k))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lpsOriginalTaylorSeries_const_mul,lpsOriginalClearedMonomial_taylor N hN]
  rfl
end QEC.Coding.TannerLiftedProduct
