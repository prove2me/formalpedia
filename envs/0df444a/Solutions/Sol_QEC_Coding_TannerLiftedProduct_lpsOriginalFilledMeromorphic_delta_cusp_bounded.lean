-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphic_delta_cusp_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:37:37.813797+00:00
-- url     : https://prove2.me/submissions/55b51f9e-569a-49cd-82ca-1ea8b9f41644

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_cusp_phase
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicDeltaQCoefficient_nome
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicDelta_cusp_coefficient
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_width_positive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_cast
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_positive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalQParam_width_pow
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
    (N : ℕ) [NeZero N] (ρ : SL(2,ℤ))
    (F : LPSOriginalFilledCurve N → ℂ) (k : ℕ)
    (hf : letI := lpsOriginalFilledTopology N
      AnalyticAt ℂ (fun q : ℂ => q^k *
      F ((lpsOriginalFilledCuspChart N (lpsOriginalCuspOrbit N ρ)).symm q)) 0) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ : ℍ =>
      ModularForm.discriminant τ ^ k *
        F (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by
  let := lpsOriginalFilledTopology N
  let c := lpsOriginalCuspOrbit N ρ
  let r := lpsOriginalCuspRepresentative N c
  let m := lpsOriginalCuspWidthNat N r
  let w := (lpsOriginalCuspGroup N r).strictWidthInfty
  have hm : 0 < m := lpsOriginalCuspWidthNat_positive N r
  have hw : 0 < w := lpsOriginalCuspGroup_width_positive N r
  obtain ⟨α,hα,hphase⟩ := lpsOriginalFilledMeromorphic_cusp_phase N ρ F
  obtain ⟨H,hH,hEq⟩ := lpsOriginalMeromorphicDelta_cusp_coefficient
    (fun q => F ((lpsOriginalFilledCuspChart N c).symm q)) k m k hm
    (by exact Nat.le_mul_of_pos_left k hm) hf α hα
  have hlim : Tendsto (fun τ : ℍ => H (Function.Periodic.qParam w (τ : ℂ)))
      UpperHalfPlane.atImInfty (𝓝 (H 0)) :=
    hH.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty hw)
  have hq (τ : ℍ) : Function.Periodic.qParam w (τ : ℂ)^m =
      Function.Periodic.qParam 1 (τ : ℂ) := by
    dsimp only [w]
    rw [lpsOriginalCuspWidthNat_cast]
    exact lpsOriginalQParam_width_pow m hm (τ : ℂ)
  have he : (fun τ : ℍ => H (Function.Periodic.qParam w (τ : ℂ))) =ᶠ[
      UpperHalfPlane.atImInfty] (fun τ : ℍ => ModularForm.discriminant τ ^ k *
        F (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by
    filter_upwards [Filter.preimage_mem_comap (Filter.Ioi_mem_atTop (1 : ℝ))] with τ hτ
    rw [hEq,hq,←lpsOriginalMeromorphicDeltaQCoefficient_nome]
    rw [←hphase ⟨τ,hτ⟩]
    rfl
  exact (hlim.isBigO_one ℝ).congr' he (Filter.EventuallyEq.refl _ _)
end QEC.Coding.TannerLiftedProduct
