-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeUpperGL_finite_qParam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:29:14.963181+00:00
-- url     : https://prove2.me/submissions/a7af63dc-1eaa-4c29-9a0b-0e820c1cf66c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperGL_finite_action
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
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime] (j : Fin p) (z : ℍ) :
    Function.Periodic.qParam 1 ((lpsHeckeUpperGL ℝ p (some j) • z:ℍ):ℂ)=
      ZMod.stdAddChar (j.val:ZMod p)*Function.Periodic.qParam (p:ℝ) (z:ℂ) := by
  rw [lpsHeckeUpperGL_finite_action]
  have he := ZMod.stdAddChar_coe (N:=p) (j.val:ℤ)
  rw [Int.cast_natCast] at he
  rw [he]
  simp only [Function.Periodic.qParam,Complex.ofReal_one,div_one,Complex.ofReal_natCast,Int.cast_natCast]
  rw [show (2:ℂ)*Real.pi*I*(((z:ℂ)+(j.val:ℂ))/(p:ℂ))=
    (2:ℂ)*Real.pi*I*(j.val:ℂ)/(p:ℂ)+(2:ℂ)*Real.pi*I*(z:ℂ)/(p:ℂ) by ring,
    Complex.exp_add]
end QEC.Coding.TannerLiftedProduct
