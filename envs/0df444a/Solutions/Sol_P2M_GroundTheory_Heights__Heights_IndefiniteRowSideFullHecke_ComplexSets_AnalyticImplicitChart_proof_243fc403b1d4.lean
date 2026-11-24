-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticImplicitChart_proof_243fc403b1d4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:18.792938+00:00
-- url     : https://prove2.me/submissions/bec5cdb5-5641-402a-835d-a44c00e57c1c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticImplicitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticImplicitChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticImplicitChart_pi_surjective_of_linearIndependent_0f35e360f3ca

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
open Topology
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AnalyticImplicitChart
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AnalyticImplicitChart
theorem _root_.solution : AnalyticImplicitChart.Statement := by
  intro σ ι _ _ h a W hh h0 hli hW
  classical
  set φ : ι → (σ → ℂ) →L[ℂ] ℂ := fun j => fderiv ℂ (h j) a with hφ
  set L : (σ → ℂ) →ₗ[ℂ] (ι → ℂ) := LinearMap.pi fun j => (φ j : (σ → ℂ) →ₗ[ℂ] ℂ) with hL
  have hLs : Function.Surjective L := pi_surjective_of_linearIndependent hli
  set K := LinearMap.ker L with hK
  obtain ⟨q, hq⟩ := K.exists_isCompl
  set d := Module.finrank ℂ K with hd'
  have hd : d + Fintype.card ι = Fintype.card σ := by
    have := L.finrank_range_add_finrank_ker
    have hKk : Module.finrank ℂ K = Module.finrank ℂ (LinearMap.ker L) := rfl
    rw [LinearMap.range_eq_top.2 hLs, finrank_top, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card] at this
    omega
  set eK : K ≃ₗ[ℂ] (Fin d → ℂ) := LinearEquiv.ofFinrankEq K (Fin d → ℂ) (by simp [d]) with heK
  set A : (σ → ℂ) →L[ℂ] (Fin d → ℂ) :=
    LinearMap.toContinuousLinearMap (eK.toLinearMap ∘ₗ K.projectionOnto q hq) with hA
  set P : (σ → ℂ) →L[ℂ] (Fin d → ℂ) × (ι → ℂ) := A.prod (ContinuousLinearMap.pi φ) with hP
  have hPinj : Function.Injective P := by
    intro z w hzw
    rw [← sub_eq_zero]
    have h1 : A (z - w) = 0 := by rw [map_sub, sub_eq_zero]; exact congrArg Prod.fst hzw
    have h2 : z - w ∈ K := by
      rw [hK, LinearMap.mem_ker]
      funext j
      have := congrFun (congrArg Prod.snd hzw) j
      simp only [hP, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply] at this
      simp [hL, map_sub, this]
    have h3 : K.projectionOnto q hq (z - w) = 0 := eK.injective (by simpa [hA] using h1)
    rw [Submodule.projectionOnto_apply_of_mem_left hq h2] at h3
    simpa using congrArg Subtype.val h3
  have hPbij : Function.Bijective (P : (σ → ℂ) →ₗ[ℂ] (Fin d → ℂ) × (ι → ℂ)) :=
    ⟨hPinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [Module.finrank_prod, hd])).1 hPinj⟩
  set Pe : (σ → ℂ) ≃L[ℂ] (Fin d → ℂ) × (ι → ℂ) :=
    (LinearEquiv.ofBijective _ hPbij).toContinuousLinearEquiv with hPe
  have hPeP : (Pe : (σ → ℂ) →L[ℂ] (Fin d → ℂ) × (ι → ℂ)) = P := by ext1 x; rfl
  set F : (σ → ℂ) → (Fin d → ℂ) × (ι → ℂ) := fun z => (A z, fun j => h j z) with hF
  have hFan : ∀ z, (∀ j, AnalyticAt ℂ (h j) z) → AnalyticAt ℂ F z := fun z hz =>
    (A.analyticAt z).prod (analyticAt_pi_iff.2 hz)
  have hFd : HasFDerivAt F (Pe : (σ → ℂ) →L[ℂ] _) a := by
    rw [hPeP]
    exact A.hasFDerivAt.prodMk (hasFDerivAt_pi.2 fun j => (hh j).differentiableAt.hasFDerivAt)
  have hst : HasStrictFDerivAt F (Pe : (σ → ℂ) →L[ℂ] _) a := by
    have := (hFan a hh).hasStrictFDerivAt; rwa [hFd.fderiv] at this
  set Φ := hst.toOpenPartialHomeomorph F with hΦ
  have hev : ∀ᶠ t in 𝓝 a, (∀ j, AnalyticAt ℂ (h j) t) ∧ t ∈ W ∧
      fderiv ℂ F t ∈ Set.range ((↑) : ((σ → ℂ) ≃L[ℂ] (Fin d → ℂ) × (ι → ℂ)) → _) := by
    refine (Filter.eventually_all.2 fun j => (hh j).eventually_analyticAt).and ((show ∀ᶠ t in 𝓝 a, t ∈ W from hW).and ?_)
    exact (hFan a hh).fderiv.continuousAt.preimage_mem_nhds
      (ContinuousLinearEquiv.isOpen.mem_nhds ⟨Pe, hFd.fderiv.symm⟩)
  obtain ⟨V₀, hV₀, hV₀o, haV₀⟩ := eventually_nhds_iff.1 hev
  set Ψ := Φ.restrOpen V₀ hV₀o with hΨ
  have hΨs : Ψ.source = Φ.source ∩ V₀ := OpenPartialHomeomorph.restrOpen_source _ _ _
  have hΨF : ∀ z, Ψ z = F z := fun z => rfl
  have haΨ : a ∈ Ψ.source := hΨs ▸ ⟨hst.mem_toOpenPartialHomeomorph_source, haV₀⟩
  have hsrc : ∀ t ∈ Ψ.source, (∀ j, AnalyticAt ℂ (h j) t) ∧ t ∈ W ∧
      fderiv ℂ F t ∈ Set.range ((↑) : ((σ → ℂ) ≃L[ℂ] (Fin d → ℂ) × (ι → ℂ)) → _) :=
    fun t ht => hV₀ t (hΨs ▸ ht).2
  set O : Set (Fin d → ℂ) := (fun y => (y, (0 : ι → ℂ))) ⁻¹' Ψ.target with hO
  refine ⟨d, A, O, Ψ.source, fun y => Ψ.symm (y, 0), hd,
    Ψ.open_target.preimage (continuous_id.prodMk continuous_const), Ψ.open_source, haΨ,
    fun t ht => (hsrc t ht).2.1, ?_, ?_, ?_⟩
  · intro y hy
    have hp : (y, (0 : ι → ℂ)) ∈ Ψ.target := hy
    obtain ⟨han, -, e', he'⟩ := hsrc _ (Ψ.map_target hp)
    have hFe : HasFDerivAt Ψ (e' : (σ → ℂ) →L[ℂ] _) (Ψ.symm (y, 0)) := by
      rw [he']; exact (hFan _ han).differentiableAt.hasFDerivAt
    have hc : ContDiffAt ℂ ω Ψ.symm (y, 0) :=
      Ψ.contDiffAt_symm hp hFe (hFan _ han).contDiffAt
    have hi : AnalyticAt ℂ (fun y : Fin d → ℂ => (y, (0 : ι → ℂ))) y :=
      analyticAt_id.prod analyticAt_const
    exact AnalyticAt.comp (g := Ψ.symm) (f := fun y : Fin d → ℂ => (y, (0 : ι → ℂ))) (x := y)
      hc.analyticAt hi
  · intro y hy
    exact congrArg Prod.fst (Ψ.right_inv (show (y, (0 : ι → ℂ)) ∈ Ψ.target from hy))
  · ext z
    constructor
    · rintro ⟨hzV, hz0⟩
      have hFz : F z = (A z, 0) := by
        simp only [hF, Prod.mk.injEq, true_and]; funext j; exact hz0 j
      refine ⟨A z, ?_, ?_⟩
      · show (A z, (0 : ι → ℂ)) ∈ Ψ.target
        rw [← hFz, ← hΨF]; exact Ψ.map_source hzV
      · show Ψ.symm (A z, 0) = z
        rw [← hFz, ← hΨF]; exact Ψ.left_inv hzV
    · rintro ⟨y, hy, rfl⟩
      have hp : (y, (0 : ι → ℂ)) ∈ Ψ.target := hy
      refine ⟨Ψ.map_target hp, fun j => ?_⟩
      have := congrFun (congrArg Prod.snd (Ψ.right_inv hp)) j
      simpa [hΨF, hF] using this
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AnalyticImplicitChart
