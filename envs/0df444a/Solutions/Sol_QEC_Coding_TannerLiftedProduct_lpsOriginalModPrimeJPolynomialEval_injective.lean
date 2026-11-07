-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalModPrimeJPolynomialEval_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:42:18.101463+00:00
-- url     : https://prove2.me/submissions/b224d88c-ed01-42b4-abc7-7d02ff5e7d2f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJZSeries_mod_constant
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPoleSeriesPolynomial_eval_eq_zero_iff
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
    Function.Injective (lpsOriginalModPrimeJPolynomialEval p) := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  have hF : PowerSeries.constantCoeff
      (PowerSeries.expand p (Fact.out : p.Prime).ne_zero
        (lpsOriginalCuspJNumerator (ZMod p)))=1 := by
    rw [PowerSeries.constantCoeff_expand]
    exact lpsOriginalJZSeries_mod_constant p
  apply (lpsOriginalPoleSeriesPolynomial_eval_eq_zero_iff
    (PowerSeries.expand p (Fact.out : p.Prime).ne_zero (lpsOriginalCuspJNumerator (ZMod p)))
    hF p (Fact.out : p.Prime).pos P).mp
  simpa only [lpsOriginalModPrimeJPolynomialEval,Polynomial.coe_eval₂RingHom,
    lpsOriginalCuspJWidth] using hP
end QEC.Coding.TannerLiftedProduct
