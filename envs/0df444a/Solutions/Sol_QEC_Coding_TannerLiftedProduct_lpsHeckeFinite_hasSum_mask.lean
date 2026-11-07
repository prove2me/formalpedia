-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeFinite_hasSum_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:31:58.667923+00:00
-- url     : https://prove2.me/submissions/17f5943c-724f-40a4-9fa4-75a09cbad5eb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperGL_finite_qParam
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePhaseFilter
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
theorem _root_.solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (z : ℍ) :
    HasSum (fun n : ℕ => if p∣n then
      PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*
        Function.Periodic.qParam (p:ℝ) (z:ℂ)^n else 0)
      ((p:ℂ)⁻¹*∑ j : Fin p,f (lpsHeckeUpperGL ℝ p (some j) • z)) := by
  classical
  have hp : (1:ℝ)∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have hs (j : Fin p) := ModularForm.hasSum_qExpansion f (by norm_num : (0:ℝ)<1) hp
    (lpsHeckeUpperGL ℝ p (some j) • z)
  have h := (hasSum_sum (s:=Finset.univ) (fun (j : Fin p) _ => hs j)).mul_left ((p:ℂ)⁻¹)
  apply h.congr_fun
  intro n
  simp_rw [lpsHeckeUpperGL_finite_qParam,mul_pow]
  rw [show (∑ j : Fin p,PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*
    (ZMod.stdAddChar (j.val:ZMod p)^n*Function.Periodic.qParam (p:ℝ) (z:ℂ)^n))=
      (PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*Function.Periodic.qParam (p:ℝ) (z:ℂ)^n)*
        (∑ j : Fin p,ZMod.stdAddChar (j.val:ZMod p)^n) by
          rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro j _;ring]
  rw [lpsHeckePhaseFilter]
  by_cases hn : p∣n
  · simp only [if_pos hn]
    have hpC : (p:ℂ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    field_simp
  · simp [hn]
end QEC.Coding.TannerLiftedProduct
