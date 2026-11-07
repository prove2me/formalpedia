-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCosetCuspData_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:41:21.279146+00:00
-- url     : https://prove2.me/submissions/6ed1462c-94a7-4a42-a478-b8181421b7d9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.KummerExtension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAffineSlopePhaseEquality
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCosetFractionRoot_injective
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
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0 < N) :
    Function.Injective (lpsOriginalCosetCuspData N hN) := by
  intro x y hxy
  let wx := lpsOriginalCosetCuspWitness N hN x
  let wy := lpsOriginalCosetCuspWitness N hN y
  have hm : wx.1.val = wy.1.val := congrArg Prod.fst hxy
  have hp : Function.Periodic.qParam 1 (wx.2.val : ℂ) =
      Function.Periodic.qParam 1 (wy.2.val : ℂ) := congrArg Prod.snd hxy
  have hpoint : ∀ τ : ℍ,
      lpsOriginalJDilated N hN (x.out.val⁻¹ • τ) =
        lpsOriginalJDilated N hN (y.out.val⁻¹ • τ) := by
    intro τ
    let A := lpsE2AffineMatrix N hN 0
    let σ : ℍ := A⁻¹ • τ
    have hσ : A • σ = τ := smul_inv_smul A τ
    have hx := wx.2.property.2.2 σ
    have hy := wy.2.property.2.2 σ
    change lpsOriginalJDilated N hN (x.out.val⁻¹ • (A • σ)) = _ at hx
    change lpsOriginalJDilated N hN (y.out.val⁻¹ • (A • σ)) = _ at hy
    rw [hσ] at hx hy
    rw [hx, hy]
    apply lpsOriginalAffineSlopePhaseEquality wx.1.val wy.1.val
      wx.1.property wy.1.property hm (wx.2.val : ℝ) (wy.2.val : ℝ) _ σ
    simpa only [Complex.ofReal_ratCast] using hp
  apply lpsOriginalCosetFractionRoot_injective N hN
  have hehol : lpsOriginalHolomorphicPullback x.out (lpsOriginalJNHolomorphic N hN) =
      lpsOriginalHolomorphicPullback y.out (lpsOriginalJNHolomorphic N hN) := by
    apply Subtype.ext
    funext τ
    exact hpoint τ
  simpa only [lpsOriginalCosetFractionRoot, lpsOriginalJNInFractionField,
    lpsOriginalFractionPullbackRing_localization] using
      congrArg (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField) hehol
end QEC.Coding.TannerLiftedProduct
