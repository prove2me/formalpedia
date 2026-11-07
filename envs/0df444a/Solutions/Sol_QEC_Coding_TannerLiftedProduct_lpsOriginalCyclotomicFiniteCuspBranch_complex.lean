-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicFiniteCuspBranch_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:42:46.945005+00:00
-- url     : https://prove2.me/submissions/f4e7a99c-bfa2-4773-bb87-8141f82242c1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicComplexRoot_phase
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspAffineBranch_taylor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_integerNumerator
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_invParameter
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_series
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicComplexEmbedding_root
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicComplexEmbedding_root_inverse
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJZSeries_mapC
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
    lpsOriginalCuspCoefficientMap (lpsOriginalCyclotomicComplexEmbedding p)
      (lpsOriginalCyclotomicFiniteCuspBranch p m)=
      lpsOriginalAnalyticCuspLocalizedTaylor
        (lpsOriginalAnalyticCuspAffineBranch 1 (by decide) ((m:ℚ)/p)) := by
  rw [lpsOriginalCyclotomicFiniteCuspBranch,map_mul,
    lpsOriginalCuspCoefficientMap_invParameter,lpsOriginalCuspCoefficientMap_series,
    map_mul,PowerSeries.map_C,pow_mul,map_pow,
    lpsOriginalCyclotomicComplexEmbedding_root_inverse]
  have he : lpsOriginalCyclotomicComplexEmbedding p
      ((AdjoinRoot.root (Polynomial.cyclotomic p ℤ))^m)=
      (lpsOriginalCyclotomicComplexRoot p)^m := by
    rw [map_pow,lpsOriginalCyclotomicComplexEmbedding_root]
  rw [←PowerSeries.rescale_map,he,lpsOriginalCuspCoefficientMap_integerNumerator,
    lpsOriginalAnalyticCuspAffineBranch_taylor]
  have hK : lpsOriginalCuspJNumerator ℂ=lpsOriginalTaylorSeries lpsOriginalJQCoefficient := by
    exact lpsOriginalJZSeries_mapC
  rw [hK,inv_pow]
  simp only [lpsOriginalCyclotomicComplexRoot_phase,PowerSeries.expand_one_apply,pow_one]
end QEC.Coding.TannerLiftedProduct
