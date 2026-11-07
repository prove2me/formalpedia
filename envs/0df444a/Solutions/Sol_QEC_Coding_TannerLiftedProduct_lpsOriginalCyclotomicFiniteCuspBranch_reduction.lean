-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicFiniteCuspBranch_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:41:43.645677+00:00
-- url     : https://prove2.me/submissions/7b2f9d94-8a96-4c7e-b486-503ca5f8a7a6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_series
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_invParameter
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicSeries_rescaleReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicReduction_root_pow
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
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime] (m : ℕ) :
    lpsOriginalCyclotomicCuspReduction p (lpsOriginalCyclotomicFiniteCuspBranch p m)=
      lpsOriginalCuspJWidth (ZMod p) 1 (by decide) := by
  change lpsOriginalCuspCoefficientMap (lpsOriginalCyclotomicReduction p) _=_
  rw [lpsOriginalCyclotomicFiniteCuspBranch,map_mul,
    lpsOriginalCuspCoefficientMap_invParameter,lpsOriginalCuspCoefficientMap_series,
    map_mul,PowerSeries.map_C,lpsOriginalCyclotomicReduction_root_pow]
  have hr := lpsOriginalCyclotomicSeries_rescaleReduction p m
  change PowerSeries.map (lpsOriginalCyclotomicReduction p)
    (PowerSeries.rescale ((AdjoinRoot.root (Polynomial.cyclotomic p ℤ))^m)
      (lpsOriginalCuspJNumerator (lpsOriginalCyclotomicCoefficientRing p)))=
      lpsOriginalCuspJNumerator (ZMod p) at hr
  rw [hr]
  simp [lpsOriginalCuspJWidth,PowerSeries.expand_one]
end QEC.Coding.TannerLiftedProduct
