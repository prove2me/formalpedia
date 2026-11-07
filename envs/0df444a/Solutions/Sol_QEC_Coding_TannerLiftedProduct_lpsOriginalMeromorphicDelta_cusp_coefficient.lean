-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicDelta_cusp_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:34:29.552249+00:00
-- url     : https://prove2.me/submissions/c2350e43-8afb-4546-89ce-f7c2f6107100

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicDeltaQCoefficient_analytic
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
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (f : ℂ → ℂ) (n m k : ℕ) (hm : 0 < m) (hnk : n ≤ m*k)
    (hf : AnalyticAt ℂ (fun q => q^n * f q) 0)
    (α : ℂ) (hα : α ≠ 0) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
      ∀ q : ℂ, H q = (q^m * lpsOriginalMeromorphicDeltaQCoefficient (q^m))^k * f (α*q) := by
  have hD : AnalyticAt ℂ
      (fun q : ℂ => lpsOriginalMeromorphicDeltaQCoefficient (q^m)) 0 :=
    lpsOriginalMeromorphicDeltaQCoefficient_analytic.fun_comp_of_eq
      (analyticAt_id.pow m) (zero_pow hm.ne')
  have hF : AnalyticAt ℂ (fun q : ℂ => (α*q)^n * f (α*q)) 0 :=
    hf.fun_comp_of_eq (analyticAt_const.mul analyticAt_id) (mul_zero α)
  let H : ℂ → ℂ := fun q => (α^n)⁻¹ * q^(m*k-n) *
    lpsOriginalMeromorphicDeltaQCoefficient (q^m)^k * ((α*q)^n * f (α*q))
  have hH : AnalyticAt ℂ H 0 :=
    (((analyticAt_const.mul (analyticAt_id.pow (m*k-n))).mul (hD.pow k)).mul hF)
  refine ⟨H,hH,?_⟩
  intro q
  calc
    H q = (α^n)⁻¹ * α^n * (q^(m*k-n)*q^n) *
        lpsOriginalMeromorphicDeltaQCoefficient (q^m)^k * f (α*q) := by
      dsimp only [H]
      rw [mul_pow]
      ring
    _ = q^(m*k) * lpsOriginalMeromorphicDeltaQCoefficient (q^m)^k * f (α*q) := by
      rw [inv_mul_cancel₀ (pow_ne_zero n hα),one_mul,←pow_add,Nat.sub_add_cancel hnk]
    _ = (q^m * lpsOriginalMeromorphicDeltaQCoefficient (q^m))^k * f (α*q) := by
      rw [mul_pow,pow_mul]
end QEC.Coding.TannerLiftedProduct
