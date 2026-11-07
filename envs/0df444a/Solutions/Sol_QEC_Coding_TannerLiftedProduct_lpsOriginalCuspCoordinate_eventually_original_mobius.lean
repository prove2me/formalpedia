-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoordinate_eventually_original_mobius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:47:41.834204+00:00
-- url     : https://prove2.me/submissions/c4cba78a-45ce-4cde-9611-d9031fb7f14f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_projection
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
theorem _root_.solution (N : ℕ) [NeZero N]
    (ρ : SL(2,ℤ)) (τ : ℍ)
    (hx : Sum.inl (Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ) ∈
        lpsOriginalFilledCuspSource N ρ) :
    ∃ g : GL (Fin 2) ℝ, g.val.det=1 ∧
      (Matrix.SpecialLinearGroup.mapGL ℝ ρ)*g∈
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ∧
      (fun z : ℂ => lpsOriginalFilledCuspPartialEquiv N ρ
        (Sum.inl (Quotient.mk (MulAction.orbitRel
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
          (UpperHalfPlane.ofComplex z)))) =ᶠ[𝓝 (τ:ℂ)]
      (fun z : ℂ => Function.Periodic.qParam (lpsOriginalCuspGroup N ρ).strictWidthInfty
        ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) := by
  let proj : ℍ → MulAction.orbitRel.Quotient
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ := Quotient.mk _
  change proj τ∈Set.range (lpsOriginalCuspProjection N ρ) at hx
  obtain ⟨σ,hσ⟩ := hx
  have ho := Quotient.eq.mp hσ
  rw [MulAction.orbitRel_apply,MulAction.mem_orbit_iff] at ho
  obtain ⟨γ,hγ⟩ := ho
  let r := Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let g := r⁻¹*γ.val
  have hστ : g • τ=σ.val := by
    dsimp only [g]
    rw [mul_smul]
    change γ.val • τ=r • σ.val at hγ
    rw [hγ]
    exact inv_smul_smul r σ.val
  have hγd : γ.val.val.det=1 := by
    obtain ⟨δ,hδ,he⟩ := γ.property
    rw [←he]
    simp only [←Matrix.GeneralLinearGroup.val_det_apply, Matrix.SpecialLinearGroup.det_mapGL, Units.val_one]
  have hd : g.val.det=1 := by
    change ((r⁻¹*γ.val).val).det=1
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, Matrix.GeneralLinearGroup.coe_inv, Matrix.det_nonsing_inv]
    have hr : r.val.det=1 := by
      simp only [r,←Matrix.GeneralLinearGroup.val_det_apply,Matrix.SpecialLinearGroup.det_mapGL,Units.val_one]
    simp only [hr,hγd,Ring.inverse_one,mul_one]
  have hu : ContinuousAt (fun z : ℂ => g • UpperHalfPlane.ofComplex z) (τ:ℂ) :=
    (continuous_const_smul g).continuousAt.comp
      (UpperHalfPlane.contMDiffAt_ofComplex (n:=ω) τ.im_pos).continuousAt
  have hnear : ∀ᶠ z in 𝓝 (τ:ℂ), 1<(g • UpperHalfPlane.ofComplex z).im := by
    apply (UpperHalfPlane.continuous_im.continuousAt.comp hu)
    change Set.Ioi 1∈𝓝 ((g • UpperHalfPlane.ofComplex (τ:ℂ)).im)
    rw [UpperHalfPlane.ofComplex_apply,hστ]
    exact isOpen_Ioi.mem_nhds σ.property
  have hr : r*g=γ.val := by dsimp only [g];group
  refine ⟨g,hd,?_,?_⟩
  · change r*g∈(CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
    rw [hr]
    exact γ.property
  · filter_upwards [hnear] with z hz
    let σz : {σ : ℍ // 1<σ.im} := ⟨g • UpperHalfPlane.ofComplex z,hz⟩
    have hp : lpsOriginalCuspProjection N ρ σz=proj (UpperHalfPlane.ofComplex z) := by
      change proj (r • (g • UpperHalfPlane.ofComplex z))=proj (UpperHalfPlane.ofComplex z)
      rw [←mul_smul,hr]
      apply Quotient.sound
      exact ⟨γ,rfl⟩
    have hf := lpsOriginalFilledCuspPartialEquiv_projection N ρ σz
    rw [hp] at hf
    exact hf
end QEC.Coding.TannerLiftedProduct
