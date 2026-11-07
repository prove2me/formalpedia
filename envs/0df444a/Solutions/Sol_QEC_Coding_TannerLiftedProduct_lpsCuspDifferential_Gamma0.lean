-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspDifferential_Gamma0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:38:40.947497+00:00
-- url     : https://prove2.me/submissions/b4b374ac-69e4-4cf6-bf3a-7a055ee11938

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferential
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspDifferential_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwo_slash_deriv
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
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (g : GL (Fin 2) ℝ)
    (hg : g∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) (τ : ℍ) (v : ℂ) :
    lpsCuspDifferential N f (g • τ)
      (deriv (fun z : ℂ => (g • UpperHalfPlane.ofComplex z : ℍ) : ℂ→ℂ) τ*v) =
    lpsCuspDifferential N f τ v := by
  have hdet : g.val.det=1 := by
    simpa only [Matrix.GeneralLinearGroup.val_det_apply,Units.val_one] using
      congrArg Units.val (Subgroup.HasDetOne.det_eq hg)
  have hs := congrFun (SlashInvariantForm.slash_action_eqn f g hg) τ
  rw [lpsWeightTwo_slash_deriv f g (by rw [hdet];norm_num)] at hs
  simpa only [lpsCuspDifferential_apply,mul_assoc] using congrArg (fun z : ℂ => z*v) hs
end QEC.Coding.TannerLiftedProduct
