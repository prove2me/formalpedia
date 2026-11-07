-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspQDifferentialCoefficient_qParam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:29:06.743682+00:00
-- url     : https://prove2.me/submissions/808c0878-8470-4911-a87c-b8e9bd570541

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.DSlope
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
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
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (τ : ℍ) :
    lpsCuspQDifferentialCoefficient N f (Function.Periodic.qParam 1 τ) =
      f τ / (((2:ℂ)*Real.pi*I)*Function.Periodic.qParam 1 τ) := by
  have hper : (1:ℝ)∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have hf0 := CuspFormClass.cuspFunction_apply_zero f (by norm_num : (0:ℝ)<1) hper
  have hq : Function.Periodic.qParam 1 (τ:ℂ)≠0 := by
    unfold Function.Periodic.qParam
    exact Complex.exp_ne_zero _
  rw [lpsCuspQDifferentialCoefficient,dslope_of_ne _ hq]
  rw [slope,hf0]
  simp only [vsub_eq_sub,sub_zero,smul_eq_mul]
  rw [UpperHalfPlane.eq_cuspFunction τ (by norm_num : (1:ℝ)≠0)
    (SlashInvariantFormClass.periodic_comp_ofComplex f hper)]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring
end QEC.Coding.TannerLiftedProduct
