-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicFormalPrimeProduct_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:44:50.664114+00:00
-- url     : https://prove2.me/submissions/fbf1a7e6-39b4-441d-8fbf-909ffa5c5254

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_jWidth
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicFiniteCuspBranch_reduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspJWidth_frobenius
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspSeries_charP
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
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime] :
    (lpsOriginalCyclotomicFormalPrimeProduct p).map (lpsOriginalCyclotomicCuspReduction p)=
      (Polynomial.X-Polynomial.C
          ((lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero)^p)) *
        (Polynomial.X^p-Polynomial.C
          (lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero)) := by
  classical
  let : CharP (lpsOriginalCuspSeriesRing (ZMod p)) p := lpsOriginalCuspSeries_charP p
  have hfinite :
      (∏ m : Fin p, (Polynomial.X-Polynomial.C (lpsOriginalCyclotomicFiniteCuspBranch p m.val))).map
        (lpsOriginalCyclotomicCuspReduction p)=
      (Polynomial.X-Polynomial.C (lpsOriginalCuspJWidth (ZMod p) 1 (by decide)))^p := by
    rw [Polynomial.map_prod]
    simp only [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
      lpsOriginalCyclotomicFiniteCuspBranch_reduction]
    simp
  have hinfty : lpsOriginalCyclotomicCuspReduction p
      (lpsOriginalCuspJWidth (lpsOriginalCyclotomicCoefficientRing p) (p*p)
        (Nat.mul_ne_zero (Fact.out : p.Prime).ne_zero (Fact.out : p.Prime).ne_zero))=
      (lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero)^p := by
    change lpsOriginalCuspCoefficientMap (lpsOriginalCyclotomicReduction p) _=_
    rw [lpsOriginalCuspCoefficientMap_jWidth]
    exact (lpsOriginalCuspJWidth_frobenius (ZMod p) p (Fact.out : p.Prime).ne_zero
      p (Fact.out : p.Prime).ne_zero).symm
  have hfinitepow :
      (lpsOriginalCuspJWidth (ZMod p) 1 (by decide))^p=
      lpsOriginalCuspJWidth (ZMod p) p (Fact.out : p.Prime).ne_zero := by
    simpa only [one_mul] using lpsOriginalCuspJWidth_frobenius (ZMod p) p
      (Fact.out : p.Prime).ne_zero 1 one_ne_zero
  rw [lpsOriginalCyclotomicFormalPrimeProduct,Polynomial.map_mul,hfinite,
    Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,hinfty,
    sub_pow_expChar,←Polynomial.C_pow,hfinitepow]
end QEC.Coding.TannerLiftedProduct
