-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspTranslateQDifferentialCoefficient_qParam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:29:16.70247+00:00
-- url     : https://prove2.me/submissions/1aa2f70b-2008-4549-a6f7-8fc4275d5378

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.DSlope
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Translate_integerPeriod
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
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (ρ : SL(2,ℤ)) (τ : ℍ) :
    lpsCuspTranslateQDifferentialCoefficient N f ρ (Function.Periodic.qParam (N:ℝ) τ) =
      (N:ℂ) * (((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ) τ) /
        (((2:ℂ)*Real.pi*I)*Function.Periodic.qParam (N:ℝ) τ) := by
  have hm : (0:ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  let ft := CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ ρ)
  have hper := lpsGamma0Translate_integerPeriod N ρ
  have hf0 := CuspFormClass.cuspFunction_apply_zero ft hm hper
  have hq : Function.Periodic.qParam (N:ℝ) (τ:ℂ)≠0 := by
    unfold Function.Periodic.qParam
    exact Complex.exp_ne_zero _
  rw [lpsCuspTranslateQDifferentialCoefficient,dslope_of_ne _ hq]
  change (N:ℂ)/((2:ℂ)*Real.pi*I) *
    slope (UpperHalfPlane.cuspFunction (N:ℝ) ft) 0 (Function.Periodic.qParam (N:ℝ) τ) = _
  rw [slope,hf0]
  simp only [vsub_eq_sub,sub_zero,smul_eq_mul]
  rw [UpperHalfPlane.eq_cuspFunction τ hm.ne'
    (SlashInvariantFormClass.periodic_comp_ofComplex ft hper)]
  have he : ft τ = ((f:ℍ→ℂ) ∣[(2:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ) τ := rfl
  rw [he]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring
end QEC.Coding.TannerLiftedProduct
