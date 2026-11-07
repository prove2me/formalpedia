-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspPullback_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:21:09.419202+00:00
-- url     : https://prove2.me/submissions/b8f839ee-4de7-4f70-b8c5-beb9b5d5575e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizedIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNormalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_width_positive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_cusp_phase
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
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (ρ : SL(2,ℤ))
    (F G : LPSOriginalFilledCurve N → ℂ)
    (he : letI := lpsOriginalFilledTopology N
      (F ∘ (lpsOriginalFilledCuspChart N (lpsOriginalCuspOrbit N ρ)).symm)
        =ᶠ[𝓝[≠] (0 : ℂ)]
      (G ∘ (lpsOriginalFilledCuspChart N (lpsOriginalCuspOrbit N ρ)).symm)) :
    (fun τ : ℍ => F (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧))
      =ᶠ[UpperHalfPlane.atImInfty]
    (fun τ : ℍ => G (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by
  let := lpsOriginalFilledTopology N
  let c := lpsOriginalCuspOrbit N ρ
  let r := lpsOriginalCuspRepresentative N c
  let w := (lpsOriginalCuspGroup N r).strictWidthInfty
  let D : LPSOriginalFilledCurve N → ℂ := fun x => F x - G x
  obtain ⟨α, hα, hphase⟩ := lpsOriginalFilledMeromorphic_cusp_phase N ρ D
  have hw : 0 < w := lpsOriginalCuspGroup_width_positive N r
  have ht : Tendsto (fun τ : ℍ => α * Function.Periodic.qParam w (τ : ℂ))
      UpperHalfPlane.atImInfty (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [mul_zero] using
        tendsto_const_nhds.mul (UpperHalfPlane.qParam_tendsto_atImInfty hw)
    · exact Filter.Eventually.of_forall (fun τ =>
        mul_ne_zero hα (Function.Periodic.qParam_ne_zero _))
  have hh := ht.eventually he
  filter_upwards [hh, Filter.preimage_mem_comap (Filter.Ioi_mem_atTop (1 : ℝ))]
    with τ hτ hhigh
  have hp := hphase ⟨τ, hhigh⟩
  change D (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧) =
    D ((lpsOriginalFilledCuspChart N c).symm
      (α * Function.Periodic.qParam w (τ : ℂ))) at hp
  change F _ = G _ at hτ
  dsimp only [D] at hp
  rw [hτ, sub_self] at hp
  exact sub_eq_zero.mp hp
end QEC.Coding.TannerLiftedProduct
