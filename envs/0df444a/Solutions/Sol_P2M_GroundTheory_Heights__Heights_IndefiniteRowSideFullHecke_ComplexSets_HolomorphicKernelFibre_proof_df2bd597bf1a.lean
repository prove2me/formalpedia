-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicKernelFibre_proof_df2bd597bf1a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:58:07.365081+00:00
-- url     : https://prove2.me/submissions/6acd6aa1-61cd-455f-9b6e-891d0fa99ea3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicKernelFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInjectiveHolomorphicInverse
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolomorphicKernelFibre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicInverse_analyticAt_of_differentiableOn_a52ac3580ddc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Filter Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace HolomorphicKernelFibre
theorem _root_.solution : HolomorphicKernelFibre.Statement := by
  intro k U f b hU hf hb d hd
  set A : (Fin k → ℂ) →L[ℂ] Fin k → ℂ := fderiv ℂ f b with hA
  have hfa : AnalyticAt ℂ f b := InjectiveHolomorphicInverse.analyticAt_of_differentiableOn hU hf hb
  have hfd : HasFDerivAt f A b := (hf.differentiableAt (hU.mem_nhds hb)).hasFDerivAt
  set W := LinearMap.range (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) with hW
  set K := LinearMap.ker (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) with hK
  obtain ⟨C, hWC⟩ := W.exists_isCompl
  obtain ⟨K', hKK'⟩ := K.exists_isCompl
  have hdimC : Module.finrank ℂ C = Module.finrank ℂ (Fin d → ℂ) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)
    have h2 := Submodule.finrank_add_eq_of_isCompl hWC
    rw [Module.finrank_fin_fun]
    rw [← hW, ← hK, hd] at h1
    omega
  have hdimK : Module.finrank ℂ K = Module.finrank ℂ (Fin d → ℂ) := by
    rw [Module.finrank_fin_fun]; exact hd
  let eC : C ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofFinrankEq _ _ hdimC
  let eK : K ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofFinrankEq _ _ hdimK
  let P : (Fin k → ℂ) →L[ℂ] Fin k → ℂ := LinearMap.toContinuousLinearMap (W.projection C hWC)
  let E : (Fin d → ℂ) →L[ℂ] Fin k → ℂ :=
    LinearMap.toContinuousLinearMap (C.subtype ∘ₗ (eC.symm : (Fin d → ℂ) →ₗ[ℂ] C))
  let lam : (Fin k → ℂ) →L[ℂ] Fin d → ℂ :=
    LinearMap.toContinuousLinearMap ((eK : K →ₗ[ℂ] Fin d → ℂ) ∘ₗ K.projectionOnto K' hKK')
  let ℓ : (Fin k → ℂ) →L[ℂ] Fin d → ℂ :=
    LinearMap.toContinuousLinearMap ((eC : C →ₗ[ℂ] Fin d → ℂ) ∘ₗ C.projectionOnto W hWC.symm)
  have hEC : ∀ t, E t ∈ C := fun t => (eC.symm t).2
  have hEinj : Function.Injective E := fun s t hst => by
    have : eC.symm s = eC.symm t := Subtype.ext hst
    exact eC.symm.injective this
  have hPE : ∀ t, P (E t) = 0 := fun t => Submodule.projection_apply_of_mem_right hWC (hEC t)
  have hPP : ∀ x, P (P x) = P x := fun x =>
    Submodule.projection_apply_of_mem_left hWC (Submodule.projection_apply_mem hWC x)
  have hPA : ∀ v, P (A v) = A v := fun v =>
    Submodule.projection_apply_of_mem_left hWC (LinearMap.mem_range_self _ v)
  have hℓA : ∀ v, ℓ (A v) = 0 := fun v => by
    have h0 : C.projectionOnto W hWC.symm (A v) = 0 :=
      Submodule.projectionOnto_apply_of_mem_right hWC.symm (LinearMap.mem_range_self _ v)
    show eC (C.projectionOnto W hWC.symm (A v)) = 0
    rw [h0, map_zero]

  let M : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ := (A : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) + (E.comp lam : _)
  have hMinj : Function.Injective M := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hv' : A v + E (lam v) = 0 := hv
    have hAv : A v = 0 := by
      refine (Submodule.disjoint_def.mp hWC.disjoint) (A v) (LinearMap.mem_range_self _ v) ?_
      rw [eq_neg_of_add_eq_zero_left hv']
      exact C.neg_mem (hEC _)
    have hlv : lam v = 0 := by
      rw [hAv, zero_add] at hv'
      exact hEinj (hv'.trans (map_zero E).symm)
    have hvK : v ∈ K := hAv
    have : eK (K.projectionOnto K' hKK' v) = 0 := hlv
    rw [Submodule.projectionOnto_apply_of_mem_left hKK' hvK, LinearEquiv.map_eq_zero_iff] at this
    exact congrArg Subtype.val this
  let M' : (Fin k → ℂ) ≃L[ℂ] Fin k → ℂ := (LinearEquiv.ofInjectiveEndo M hMinj).toContinuousLinearEquiv
  let Φ : (Fin k → ℂ) → Fin k → ℂ := fun z => P (f z) + E (lam z)
  have hΦd : HasFDerivAt Φ (M' : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) b := by
    have h := (P.hasFDerivAt.comp b hfd).add (E.comp lam).hasFDerivAt
    have hM : P.comp A + E.comp lam = (M' : (Fin k → ℂ) →L[ℂ] Fin k → ℂ) := by
      ext1 v
      show P (A v) + E (lam v) = A v + E (lam v)
      rw [hPA]
    rw [hM] at h
    exact h
  have hΦc : ContDiffAt ℂ 1 Φ b :=
    (P.contDiff.contDiffAt.comp b hfa.contDiffAt).add (E.comp lam).contDiff.contDiffAt
  let H := hΦc.toOpenPartialHomeomorph Φ hΦd one_ne_zero
  have hHΦ : ∀ z, H z = Φ z := fun z => rfl
  have hbS : b ∈ H.source := hΦc.mem_toOpenPartialHomeomorph_source hΦd one_ne_zero
  have hΦbT : Φ b ∈ H.target := hΦc.image_mem_toOpenPartialHomeomorph_target hΦd one_ne_zero
  have hinv : ContDiffAt ℂ 1 H.symm (Φ b) := hΦc.to_localInverse hΦd one_ne_zero
  have hHb : H.symm (Φ b) = b := by rw [← hHΦ]; exact H.left_inv hbS
  obtain ⟨O, hO, hOo, hbO⟩ := eventually_nhds_iff.mp (hinv.eventually (by simp))
  set c := P (f b) with hc
  let T := (H.target ∩ H.symm ⁻¹' U) ∩ O
  have hTo : IsOpen T := (H.isOpen_inter_preimage_symm hU).inter hOo
  let aff : (Fin d → ℂ) → Fin k → ℂ := fun t => c + E t
  have haff : Continuous aff := continuous_const.add E.continuous
  refine ⟨aff ⁻¹' T, lam b, fun t => H.symm (aff t), ℓ, hTo.preimage haff, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show c + E (lam b) ∈ T
    refine ⟨⟨hΦbT, ?_⟩, hbO⟩
    show H.symm (Φ b) ∈ U
    rw [hHb]; exact hb
  · intro t ht
    exact ((hO _ ht.2).differentiableAt one_ne_zero).comp t
      ((differentiableAt_const c).add E.differentiableAt) |>.differentiableWithinAt
  · intro t ht
    exact ht.1.2
  · intro s hs t ht hst
    have h1 := H.right_inv hs.1.1
    have h2 := H.right_inv ht.1.1
    have : aff s = aff t := by rw [← h1, ← h2]; exact congrArg H hst
    exact hEinj (add_left_cancel this)
  ·
    have hfib : ∀ t ∈ aff ⁻¹' T, P (f (H.symm (aff t))) = c := by
      intro t ht
      have h1 : Φ (H.symm (aff t)) = c + E t := H.right_inv ht.1.1
      have h2 := congrArg P h1
      simp only [Φ, map_add, hPE, add_zero, hPP] at h2
      rw [h2, hc, hPP]
    intro s hs t ht hst
    have hq : C.projectionOnto W hWC.symm (f (H.symm (aff s))) =
        C.projectionOnto W hWC.symm (f (H.symm (aff t))) := eC.injective hst
    rw [← Submodule.projection_add_projection_eq_self hWC (f (H.symm (aff s))),
      ← Submodule.projection_add_projection_eq_self hWC (f (H.symm (aff t)))]
    have hs' := hfib s hs
    have ht' := hfib t ht
    simp only [P, LinearMap.coe_toContinuousLinearMap'] at hs' ht'
    rw [hs', ht', Submodule.projection_apply, Submodule.projection_apply (q := W), hq]
  ·
    have hγy : H.symm (aff (lam b)) = b := hHb
    have hγd : DifferentiableAt ℂ (fun t => H.symm (aff t)) (lam b) :=
      (hinv.differentiableAt one_ne_zero).comp (lam b) ((differentiableAt_const c).add E.differentiableAt)
    have hfd' : HasFDerivAt f A (H.symm (aff (lam b))) := by rw [hγy]; exact hfd
    have h := ℓ.hasFDerivAt.comp (lam b) (hfd'.comp (lam b) hγd.hasFDerivAt)
    refine h.fderiv.trans ?_
    ext1 v
    exact hℓA _
end HolomorphicKernelFibre
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
