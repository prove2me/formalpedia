-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHecke_differential_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:40:51.811655+00:00
-- url     : https://prove2.me/submissions/8821fcfb-d458-476d-83ed-4cf194f20a7d

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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperGL_det
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
theorem _root_.solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (τ : ℍ) (v : ℂ) :
    lpsCuspDifferential N (lpsCuspHeckeLinearMap N p hNp f) τ v =
      ∑i : Option (Fin p),lpsCuspDifferential N f (lpsHeckeUpperGL ℝ p i • τ)
        (deriv (fun z : ℂ => (lpsHeckeUpperGL ℝ p i • UpperHalfPlane.ofComplex z : ℍ) : ℂ→ℂ) τ*v) := by
  change lpsHeckeSlashSum p f τ * v = _
  simp only [lpsHeckeSlashSum,Finset.sum_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hp : 0<(lpsHeckeUpperGL ℝ p i).val.det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply,lpsHeckeUpperGL_det]
    exact_mod_cast (Fact.out : p.Prime).pos
  rw [lpsWeightTwo_slash_deriv f _ hp,lpsCuspDifferential_apply,mul_assoc]
end QEC.Coding.TannerLiftedProduct
