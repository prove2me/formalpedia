-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalDualMonicRelation_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:01:34.061408+00:00
-- url     : https://prove2.me/submissions/14567680-75f7-469a-b1df-08eeadbad0d5

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
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
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    (P : Polynomial (Polynomial F)) (hP : P.Monic)
    (x y : K)
    (hroot : P.eval₂ (Polynomial.eval₂RingHom (algebraMap F K) y) x = 0)
    (hx : Transcendental F x) : Transcendental F y := by
  intro hy
  let E := Algebra.adjoin F ({y} : Set K)
  let : Module.Finite F E := Algebra.finite_adjoin_simple_of_isIntegral hy.isIntegral
  let ys : E := ⟨y,Algebra.subset_adjoin (by simp)⟩
  let c : Polynomial F →+* E := Polynomial.eval₂RingHom (algebraMap F E) ys
  have hc : (algebraMap E K).comp c = Polynomial.eval₂RingHom (algebraMap F K) y := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [c,RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C]
      change algebraMap E K (algebraMap F E a) = algebraMap F K a
      exact (IsScalarTower.algebraMap_apply F E K a).symm
    · simp only [c,RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
      change (ys : K) = y
      rfl
  have hxi : IsIntegral E x := by
    refine ⟨P.map c,hP.map c,?_⟩
    change (P.map c).eval₂ (algebraMap E K) x = 0
    rw [Polynomial.eval₂_map,hc]
    exact hroot
  exact hx (isIntegral_trans (R := F) x hxi).isAlgebraic
end QEC.Coding.TannerLiftedProduct
