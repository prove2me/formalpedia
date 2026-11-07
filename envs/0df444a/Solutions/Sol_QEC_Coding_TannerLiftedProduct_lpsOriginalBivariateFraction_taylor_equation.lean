-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalBivariateFraction_taylor_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:37:06.182499+00:00
-- url     : https://prove2.me/submissions/2c01ec65-e7e0-479a-8880-2ecc1d7babc5

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedCusp_pullback_of_bound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalBivariateHolomorphicEval_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroGerm_of_puncturedDisk
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFiniteClearedComplexSum_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedCusp_support_sum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilated_qParam_pullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQCoefficient_analytic_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQSeries_dilated_map
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPower_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_qpow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_sub
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_zero_iff_germ
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (G H : Polynomial (Polynomial ℂ)) (B : ℕ)
    (hG : lpsOriginalClearingBound M G ≤ B)
    (hH : lpsOriginalClearingBound M H ≤ B)
    (he : lpsOriginalJNHolomorphic N hN *
        lpsOriginalBivariateHolomorphicEval M hM H =
      lpsOriginalBivariateHolomorphicEval M hM G) :
    PowerSeries.map (algebraMap ℚ ℂ) (PowerSeries.X ^ N) *
        lpsOriginalTaylorSeries (lpsOriginalClearedCusp M B G) =
      PowerSeries.map (algebraMap ℚ ℂ)
          (PowerSeries.expand N (Nat.ne_of_gt hN) lpsOriginalJQSeries) *
        lpsOriginalTaylorSeries (lpsOriginalClearedCusp M B H) := by
  let KN : ℂ → ℂ := fun q => lpsOriginalJQCoefficient (q ^ N)
  let D := (fun q : ℂ => q ^ N) * lpsOriginalClearedCusp M B G -
    KN * lpsOriginalClearedCusp M B H
  have haG : AnalyticAt ℂ (lpsOriginalClearedCusp M B G) 0 := by
    rw [lpsOriginalClearedCusp_support_sum]
    exact lpsOriginalFiniteClearedComplexSum_analytic M (Nat.ne_of_gt hM) B
      (fun s : LPSOriginalBivariateSupport G => s.2.val)
      (fun s : LPSOriginalBivariateSupport G => s.1.val)
      (fun s : LPSOriginalBivariateSupport G => (G.coeff s.1.val).coeff s.2.val)
  have haH : AnalyticAt ℂ (lpsOriginalClearedCusp M B H) 0 := by
    rw [lpsOriginalClearedCusp_support_sum]
    exact lpsOriginalFiniteClearedComplexSum_analytic M (Nat.ne_of_gt hM) B
      (fun s : LPSOriginalBivariateSupport H => s.2.val)
      (fun s : LPSOriginalBivariateSupport H => s.1.val)
      (fun s : LPSOriginalBivariateSupport H => (H.coeff s.1.val).coeff s.2.val)
  have hKN : AnalyticAt ℂ KN 0 :=
    lpsOriginalJQCoefficient_analytic_zero.comp_of_eq
      (lpsOriginalPower_analytic N) (zero_pow (Nat.ne_of_gt hN))
  have haD : AnalyticAt ℂ D 0 :=
    ((lpsOriginalPower_analytic N).mul haG).sub (hKN.mul haH)
  have hg : D =ᶠ[𝓝 0] 0 := by
    apply lpsOriginalZeroGerm_of_puncturedDisk haD
    intro q hq hq0
    let τ : ℍ := ⟨Function.Periodic.invQParam 1 q,
      Function.Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num) hq hq0⟩
    have hqτ : Function.Periodic.qParam 1 (τ : ℂ) = q :=
      Function.Periodic.qParam_right_inv (by norm_num) hq0
    change q ^ N * lpsOriginalClearedCusp M B G q -
      lpsOriginalJQCoefficient (q ^ N) * lpsOriginalClearedCusp M B H q = 0
    rw [← hqτ,
      lpsOriginalClearedCusp_pullback_of_bound M hM B G hG τ,
      lpsOriginalClearedCusp_pullback_of_bound M hM B H hH τ,
      ← lpsOriginalJDilated_qParam_pullback N hN τ]
    have heτ := congrArg (fun F : LPSOriginalHolomorphicRing => F.val τ) he
    change lpsOriginalJDilated N hN τ *
      (lpsOriginalBivariateHolomorphicEval M hM H).val τ =
        (lpsOriginalBivariateHolomorphicEval M hM G).val τ at heτ
    rw [lpsOriginalBivariateHolomorphicEval_apply,
      lpsOriginalBivariateHolomorphicEval_apply] at heτ
    rw [← heτ]
    ring
  have ht := (lpsOriginalTaylorSeries_zero_iff_germ haD).mpr hg
  rw [lpsOriginalTaylorSeries_sub ((lpsOriginalPower_analytic N).mul haG) (hKN.mul haH),
    lpsOriginalTaylorSeries_mul (lpsOriginalPower_analytic N) haG,
    lpsOriginalTaylorSeries_mul hKN haH,
    lpsOriginalTaylorSeries_qpow] at ht
  simpa only [KN, map_pow, PowerSeries.map_X,
    lpsOriginalJQSeries_dilated_map] using sub_eq_zero.mp ht
end QEC.Coding.TannerLiftedProduct
