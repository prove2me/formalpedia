-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_Kronecker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:41:21.59407+00:00
-- url     : https://prove2.me/submissions/489e09f2-cdee-4cdc-a862-19411c06ed7f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModPrimeJPolynomialEval_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModPrimeJPolynomialEval_integerCoeff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModPrimeJPolynomialEval_X
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_modSeriesFactorization
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
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))=
      (Polynomial.X-Polynomial.C ((Polynomial.X : Polynomial (ZMod p))^p)) *
        (Polynomial.X^p-Polynomial.C (Polynomial.X : Polynomial (ZMod p))) := by
  apply Polynomial.map_injective (lpsOriginalModPrimeJPolynomialEval p)
    (lpsOriginalModPrimeJPolynomialEval_injective p)
  rw [Polynomial.map_map,lpsOriginalModPrimeJPolynomialEval_integerCoeff]
  simp only [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
    Polynomial.map_pow,map_pow,lpsOriginalModPrimeJPolynomialEval_X]
  simpa only [map_pow] using lpsOriginalPrimeIntegerPolynomial_modSeriesFactorization p
end QEC.Coding.TannerLiftedProduct
