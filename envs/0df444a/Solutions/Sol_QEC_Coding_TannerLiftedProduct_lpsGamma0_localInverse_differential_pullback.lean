-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0_localInverse_differential_pullback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:45:30.3532+00:00
-- url     : https://prove2.me/submissions/555a577b-c433-45e6-8fd4-e9e680258a92

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspDifferential_Gamma0
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspDifferential_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0_lifts_eventually_smul
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 4∣N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (σ τ : ℍ)
    (hs : Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ∈
      ((lpsGamma0_quotient_localHomeomorph N hN).localInverseAt σ).source) :
    let e := (lpsGamma0_quotient_localHomeomorph N hN).localInverseAt σ
    let proj := Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    f (e (proj τ)) * deriv (fun z : ℂ => (e (proj (UpperHalfPlane.ofComplex z)) : ℂ)) τ =
      f τ := by
  let hf := lpsGamma0_quotient_localHomeomorph N hN
  let e := hf.localInverseAt σ
  let proj := Quotient.mk (MulAction.orbitRel
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
  let u : ℂ→ℍ := UpperHalfPlane.ofComplex
  let v : ℂ→ℍ := fun z => e (proj (u z))
  have hu : ContinuousAt u (τ:ℂ) :=
    (UpperHalfPlane.contMDiffAt_ofComplex (n:=ω) τ.im_pos).continuousAt
  have hproj : Continuous proj := continuous_quot_mk
  have ht : proj (u τ)=proj τ := by simp [u]
  have hv : ContinuousAt v (τ:ℂ) := by
    apply (e.continuousAt (by simpa only [ht] using hs)).comp
    exact hproj.continuousAt.comp hu
  have he : (fun z => proj (v z)) =ᶠ[𝓝 (τ:ℂ)] (fun z => proj (u z)) := by
    have hsrc : ∀ᶠ z in 𝓝 (τ:ℂ), proj (u z)∈e.source := by
      apply hproj.continuousAt.comp hu
      change e.source∈𝓝 (proj (u τ))
      exact e.open_source.mem_nhds (by simpa only [ht] using hs)
    filter_upwards [hsrc] with z hz
    exact hf.apply_localInverseAt_of_mem hz
  obtain ⟨γ,hγ⟩ := lpsGamma0_lifts_eventually_smul N hN u v τ hu hv he
  have hec : (fun z => (v z:ℂ)) =ᶠ[𝓝 (τ:ℂ)]
      (fun z => (γ.val • UpperHalfPlane.ofComplex z : ℍ)) := by
    filter_upwards [hγ] with z hz
    exact congrArg UpperHalfPlane.coe hz
  have hg := lpsCuspDifferential_Gamma0 N f γ.val γ.property τ 1
  have h0 : f (v (τ:ℂ)) * deriv (fun z => (v z:ℂ)) τ = f τ := by
    rw [hγ.eq_of_nhds,hec.deriv_eq]
    simp only [u,UpperHalfPlane.ofComplex_apply]
    simpa only [lpsCuspDifferential_apply,mul_one] using hg
  simpa only [v,u,UpperHalfPlane.ofComplex_apply] using h0
end QEC.Coding.TannerLiftedProduct
