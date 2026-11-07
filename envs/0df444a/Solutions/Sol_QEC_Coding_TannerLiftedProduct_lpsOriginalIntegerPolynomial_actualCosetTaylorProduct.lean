-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerPolynomial_actualCosetTaylorProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:41:55.932925+00:00
-- url     : https://prove2.me/submissions/e2efd09b-36ce-48fe-9114-e72087f44833

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCoprimeModularReduction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_pointwiseProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCosetBranch_nome
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticLevelCoefficientEval_nome
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAnalyticCuspLocalizedTaylor_zero_of_nome
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
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := Fintype.ofFinite (LPSOriginalCuspIndex N)
    ((lpsOriginalIntegerPolynomial N hN).map
      (lpsOriginalAnalyticLevelCoefficientEval N hN)).map
        lpsOriginalAnalyticCuspLocalizedTaylor =
      ∏ x : LPSOriginalCuspIndex N, (Polynomial.X - Polynomial.C
        (lpsOriginalAnalyticCuspLocalizedTaylor (lpsOriginalAnalyticCosetBranch N hN x))) := by
  classical
  let := Fintype.ofFinite (LPSOriginalCuspIndex N)
  let D := (lpsOriginalIntegerPolynomial N hN).map
      (lpsOriginalAnalyticLevelCoefficientEval N hN) -
      ∏ x : LPSOriginalCuspIndex N,
        (Polynomial.X - Polynomial.C (lpsOriginalAnalyticCosetBranch N hN x))
  have hzero : D.map lpsOriginalAnalyticCuspLocalizedTaylor = 0 := by
    ext k
    rw [Polynomial.coeff_map,Polynomial.coeff_zero]
    apply lpsOriginalAnalyticCuspLocalizedTaylor_zero_of_nome
    intro τ
    rw [← Polynomial.coeff_map]
    have hc : D.map (lpsOriginalAnalyticCuspLocalizedNomeEval τ) = 0 := by
      dsimp only [D]
      rw [Polynomial.map_sub,Polynomial.map_map,
        lpsOriginalAnalyticLevelCoefficientEval_nome,Polynomial.map_prod]
      rw [lpsOriginalIntegerPolynomial_pointwiseProduct N hN
        (lpsE2AffineMatrix N hN 0 • τ)]
      apply sub_eq_zero.mpr
      apply Finset.prod_congr rfl
      intro x _
      rw [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
        lpsOriginalAnalyticCosetBranch_nome]
    rw [hc,Polynomial.coeff_zero]
  dsimp only [D] at hzero
  rw [Polynomial.map_sub,Polynomial.map_prod] at hzero
  simpa only [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C]
    using sub_eq_zero.mp hzero
end QEC.Coding.TannerLiftedProduct
