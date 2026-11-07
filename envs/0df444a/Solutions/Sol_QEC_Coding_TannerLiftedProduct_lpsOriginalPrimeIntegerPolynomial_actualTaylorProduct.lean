-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_actualTaylorProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:34:20.548753+00:00
-- url     : https://prove2.me/submissions/190ae68d-3fa0-41e5-a76d-a640ae873003

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeCuspCorrespondence
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticPrimeBranch_nome
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticPrimeCoefficientEval_nome
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspLocalizedTaylor_zero_of_nome
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_pointwiseProduct
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
    ((lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      (lpsOriginalAnalyticPrimeCoefficientEval p)).map lpsOriginalAnalyticCuspLocalizedTaylor=
      ∏ i : Option (Fin p), (Polynomial.X-Polynomial.C
        (lpsOriginalAnalyticCuspLocalizedTaylor (lpsOriginalAnalyticPrimeBranch p i))) := by
  classical
  let D := (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      (lpsOriginalAnalyticPrimeCoefficientEval p)-
      ∏ i : Option (Fin p), (Polynomial.X-Polynomial.C (lpsOriginalAnalyticPrimeBranch p i))
  have hzero : D.map lpsOriginalAnalyticCuspLocalizedTaylor=0 := by
    ext k
    rw [Polynomial.coeff_map,Polynomial.coeff_zero]
    apply lpsOriginalAnalyticCuspLocalizedTaylor_zero_of_nome
    intro τ
    rw [←Polynomial.coeff_map]
    have hc : D.map (lpsOriginalAnalyticCuspLocalizedNomeEval τ)=0 := by
      dsimp only [D]
      rw [Polynomial.map_sub,Polynomial.map_map,
        lpsOriginalAnalyticPrimeCoefficientEval_nome,Polynomial.map_prod]
      have h:=lpsOriginalPrimeIntegerPolynomial_pointwiseProduct p
        (lpsE2AffineMatrix p (Fact.out : p.Prime).pos 0 • τ)
      rw [h]
      apply sub_eq_zero.mpr
      apply Finset.prod_congr rfl
      intro i _
      rw [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
        lpsOriginalAnalyticPrimeBranch_nome]
    rw [hc,Polynomial.coeff_zero]
  dsimp only [D] at hzero
  rw [Polynomial.map_sub,Polynomial.map_prod] at hzero
  simpa only [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C]
    using sub_eq_zero.mp hzero
end QEC.Coding.TannerLiftedProduct
