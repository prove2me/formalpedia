-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_proof_of_framePlaneGraph_9186241062c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:25:29.573588+00:00
-- url     : https://prove2.me/submissions/9ce661db-db66-4c39-8710-27e70aacbf66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyTangentGraphDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZeroSetOpenMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFramePlaneGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFramePlaneGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameGraphGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameJacobianGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PJacobianRankGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PConormalGenerationGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameImplicitGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNullSmaller
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarietyTangentGraphDense
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_frameProjCLM_apply_b4ab43f50eca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_isClosed_zeroSetEuc_be2830816704
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_exists_near_off_c08368d72ca2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_analyticAt_of_differentiableOn_76a8176a8caf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_exists_tangent_frame_31c57c5b4317
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mono
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Topology Filter MeasureTheory
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace VarietyTangentGraphDense
theorem _root_.solution (hP : FramePlaneGraph.Statement)
    (hO : IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.Statement) : VarietyTangentGraphDense.Statement := by
  classical
  open VarietyTangentGraphDense in
  intro n d J hJ hd z hz ε hε
  obtain ⟨I₀, J', hcard, hJ'd, hloc⟩ := hP n d J hJ hd (EuclideanSpace.basisFun (Fin n) ℂ)
  set b₀ := EuclideanSpace.basisFun (Fin n) ℂ with hb₀
  obtain ⟨z₁, hz₁, hz₁z⟩ := exists_near_off hO hJ hd hJ'd hz hε
  obtain ⟨Ω, V, g, hΩ, hV, hz₁V, hg, hpg, hgraph⟩ := hloc z₁ hz₁
  obtain ⟨w₁, hw₁, rfl⟩ : z₁ ∈ g '' Ω := by
    rw [← hgraph]
    exact ⟨hz₁, hz₁V⟩
  have hgd : ∀ w ∈ Ω, HasFDerivAt g (fderiv ℂ g w) w := fun w hw =>
    (hg.differentiableAt (hΩ.mem_nhds hw)).hasFDerivAt
  set L := fderiv ℂ g w₁ with hLdef
  set P₀ := frameProjCLM b₀ I₀ with hP₀
  have hPL : P₀.comp L = ContinuousLinearMap.id ℂ (I₀ → ℂ) := by
    have h1 : HasFDerivAt (fun w => P₀ (g w)) (P₀.comp L) w₁ := P₀.hasFDerivAt.comp w₁ (hgd w₁ hw₁)
    have h2 : HasFDerivAt (fun w => P₀ (g w)) (ContinuousLinearMap.id ℂ (I₀ → ℂ)) w₁ := by
      refine (hasFDerivAt_id w₁).congr_of_eventuallyEq ?_
      filter_upwards [hΩ.mem_nhds hw₁] with w hw
      rw [hP₀, frameProjCLM_apply, hpg w hw]
      rfl
    exact h1.unique h2
  have hLinj : Function.Injective L := fun u v huv => by
    have h := congrArg P₀ huv
    rwa [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, hPL] at h
  obtain ⟨b, hbT, hbinj⟩ := exists_tangent_frame I₀ L hLinj
  set P := frameProjCLM b I₀ with hPdef
  set φ : (I₀ → ℂ) → (I₀ → ℂ) := fun w => P (g w) with hφdef
  let M₀ : (I₀ → ℂ) ≃ₗ[ℂ] (I₀ → ℂ) :=
    LinearEquiv.ofInjectiveEndo ((P.comp L : (I₀ → ℂ) →L[ℂ] (I₀ → ℂ)) : (I₀ → ℂ) →ₗ[ℂ] (I₀ → ℂ)) hbinj
  let M : (I₀ → ℂ) ≃L[ℂ] (I₀ → ℂ) := M₀.toContinuousLinearEquiv
  have hMc : (M : (I₀ → ℂ) →L[ℂ] (I₀ → ℂ)) = P.comp L := ContinuousLinearMap.ext fun v => rfl
  have hφd : HasFDerivAt φ (M : (I₀ → ℂ) →L[ℂ] (I₀ → ℂ)) w₁ := by
    rw [hMc]
    exact P.hasFDerivAt.comp w₁ (hgd w₁ hw₁)
  have hgan := analyticAt_of_differentiableOn hΩ hg hw₁
  have hφc : ContDiffAt ℂ 1 φ w₁ := ((P.analyticAt (g w₁)).comp hgan).contDiffAt
  set e := hφc.toOpenPartialHomeomorph φ hφd one_ne_zero with he
  set ψ := hφc.localInverse hφd one_ne_zero with hψ
  have hψe : ψ = e.symm := rfl
  have hw₁s : w₁ ∈ e.source := hφc.mem_toOpenPartialHomeomorph_source hφd one_ne_zero
  have hy₁t : φ w₁ ∈ e.target := hφc.image_mem_toOpenPartialHomeomorph_target hφd one_ne_zero
  have hψy₁ : ψ (φ w₁) = w₁ := hφc.localInverse_apply_image hφd one_ne_zero
  have hψc : ContDiffAt ℂ 1 ψ (φ w₁) := hφc.to_localInverse hφd one_ne_zero
  have hD : ∀ᶠ y in 𝓝 (φ w₁), DifferentiableAt ℂ ψ y :=
    (hψc.eventually (by simp)).mono fun y hy => hy.differentiableAt one_ne_zero
  set S₀ := e.target ∩ e.symm ⁻¹' Ω with hS₀def
  have hS₀ : IsOpen S₀ := e.isOpen_inter_preimage_symm hΩ
  have hy₁S₀ : φ w₁ ∈ S₀ := by
    refine ⟨hy₁t, ?_⟩
    show e.symm (φ w₁) ∈ Ω
    rw [← hψe, hψy₁]
    exact hw₁
  set Ω' := interior (S₀ ∩ {y | DifferentiableAt ℂ ψ y}) with hΩ'def
  have hΩ' : IsOpen Ω' := isOpen_interior
  have hy₁Ω' : φ w₁ ∈ Ω' := mem_interior_iff_mem_nhds.2 (Filter.inter_mem (hS₀.mem_nhds hy₁S₀) hD)
  have hΩ'sub : ∀ y ∈ Ω', y ∈ e.target ∧ ψ y ∈ Ω ∧ DifferentiableAt ℂ ψ y := fun y hy => by
    have h := interior_subset hy
    exact ⟨h.1.1, h.1.2, h.2⟩
  set Ω₁ := e.source ∩ e ⁻¹' Ω' with hΩ₁def
  have hΩ₁ : IsOpen Ω₁ := e.isOpen_inter_preimage hΩ'
  set V' := V ∩ (zeroSetEuc J')ᶜ ∩ P₀ ⁻¹' Ω₁ with hV'def
  have hV' : IsOpen V' :=
    (hV.inter (isClosed_zeroSetEuc J').isOpen_compl).inter (hΩ₁.preimage P₀.continuous)
  refine ⟨b, I₀, Ω', V', fun y => g (ψ y), φ w₁, hcard, hΩ', hV', hy₁Ω', ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨-, hψΩ, hψd⟩ := hΩ'sub y hy
    exact ((hg.differentiableAt (hΩ.mem_nhds hψΩ)).comp y hψd).differentiableWithinAt
  · intro y hy
    rw [← frameProjCLM_apply]
    exact e.right_inv (hΩ'sub y hy).1
  · ext x
    constructor
    · rintro ⟨hxZ, ⟨⟨hxV, hxZ'⟩, hxΩ₁⟩⟩
      obtain ⟨w, hw, rfl⟩ : x ∈ g '' Ω := by
        rw [← hgraph]
        exact ⟨⟨hxZ, hxZ'⟩, hxV⟩
      have hPw : P₀ (g w) = w := by
        rw [hP₀, frameProjCLM_apply]
        exact hpg w hw
      have hwΩ₁ : w ∈ Ω₁ := by
        have h : P₀ (g w) ∈ Ω₁ := hxΩ₁
        rwa [hPw] at h
      refine ⟨e w, hwΩ₁.2, ?_⟩
      show g (ψ (e w)) = g w
      rw [hψe, e.left_inv hwΩ₁.1]
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hyt, hψΩ, -⟩ := hΩ'sub y hy
      have hmem : g (ψ y) ∈ (zeroSetEuc J \ zeroSetEuc J') ∩ V := by
        rw [hgraph]
        exact ⟨ψ y, hψΩ, rfl⟩
      refine ⟨hmem.1.1, ⟨hmem.2, hmem.1.2⟩, ?_⟩
      show P₀ (g (ψ y)) ∈ Ω₁
      rw [hP₀, frameProjCLM_apply, hpg _ hψΩ]
      refine ⟨e.map_target hyt, ?_⟩
      show e (e.symm y) ∈ Ω'
      rw [e.right_inv hyt]
      exact hy
  · intro j hj
    have hψd : HasFDerivAt ψ (fderiv ℂ ψ (φ w₁)) (φ w₁) := (hψc.differentiableAt one_ne_zero).hasFDerivAt
    have hgd' : HasFDerivAt g L (ψ (φ w₁)) := by
      rw [hψy₁]
      exact hgd w₁ hw₁
    have hcomp := (innerSL ℂ (b j)).hasFDerivAt.comp (φ w₁) (hgd'.comp (φ w₁) hψd)
    have hzero : (innerSL ℂ (b j)).comp (L.comp (fderiv ℂ ψ (φ w₁))) = 0 :=
      ContinuousLinearMap.ext fun v => by simp [hbT j hj]
    rw [hzero] at hcomp
    have hfun : (fun y => inner ℂ (b j) (g (ψ y))) = ⇑(innerSL ℂ (b j)) ∘ g ∘ ψ := by
      funext y
      simp
    rw [hfun]
    exact hcomp.fderiv
  · show dist (g (ψ (φ w₁))) z < ε
    rw [hψy₁]
    exact hz₁z
end VarietyTangentGraphDense
end GroundTheory.Heights₂.Heights
