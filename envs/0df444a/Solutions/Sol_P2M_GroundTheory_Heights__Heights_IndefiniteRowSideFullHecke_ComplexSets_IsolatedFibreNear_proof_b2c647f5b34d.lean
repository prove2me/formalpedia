-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsolatedFibreNear_proof_b2c647f5b34d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:58:50.707985+00:00
-- url     : https://prove2.me/submissions/9cad4d7e-30b2-496a-a1f8-965852161bae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCompactHolomorphicFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedFibreNear

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
open Topology Metric Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace IsolatedFibreNear
theorem _root_.solution (hFin : CompactHolomorphicFibreFinite.Statement) :
    IsolatedFibreNear.Statement := by
  intro σ _ X w d A hX hiso
  obtain ⟨N, k, f, hN, hwN, hf, hXN⟩ := hX
  obtain ⟨W, hW, hWiso⟩ := hiso
  have memX : ∀ z, z ∈ N → (∀ i, f i z = 0) → z ∈ X := fun z hz h0 => by
    have : z ∈ X ∩ N := by rw [hXN]; exact ⟨hz, h0⟩
    exact this.1
  have zerosX : ∀ z, z ∈ X → z ∈ N → ∀ i, f i z = 0 := fun z hzX hzN => by
    have : z ∈ X ∩ N := ⟨hzX, hzN⟩
    rw [hXN] at this
    exact this.2
  obtain ⟨r, hr, hrsub⟩ := (nhds_basis_closedBall (x := w)).mem_iff.1 (inter_mem (hN.mem_nhds hwN) hW)
  have hBN : closedBall w r ⊆ N := fun z hz => (hrsub hz).1
  have hBW : closedBall w r ⊆ W := fun z hz => (hrsub hz).2

  set g : (σ → ℂ) → (Fin k → ℂ) := fun z i => f i z with hg
  have hgc : ContinuousOn g (closedBall w r) :=
    continuousOn_pi.2 fun i => ((hf i).continuousOn).mono hBN
  set K := sphere w r ∩ g ⁻¹' {0} with hK
  have hKc : IsCompact K := by
    refine (isCompact_sphere w r).of_isClosed_subset ?_ Set.inter_subset_left
    exact (hgc.mono sphere_subset_closedBall).preimage_isClosed_of_isClosed isClosed_sphere isClosed_singleton
  have hAK : A w ∉ A '' K := by
    rintro ⟨z, ⟨hzs, hz0⟩, hzA⟩
    have hzB : z ∈ closedBall w r := sphere_subset_closedBall hzs
    have hz0' : ∀ i, f i z = 0 := fun i => congrFun hz0 i
    have hzw : z = w := hWiso z ⟨memX z (hBN hzB) hz0', hBW hzB⟩ hzA
    rw [mem_sphere, hzw, dist_self] at hzs
    exact hr.ne hzs
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.isOpen_iff.1 ((hKc.image A.continuous).isClosed.isOpen_compl) (A w) hAK
  refine ⟨ball w r ∩ A ⁻¹' ball (A w) ε, ?_, ?_⟩
  · exact inter_mem (ball_mem_nhds w hr) (A.continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hε))
  rintro x ⟨hxX, hxB, hxD⟩

  set F := {z | z ∈ ball w r ∧ (∀ i, f i z = 0) ∧ A z = A x} with hF
  have hFeq : F = closedBall w r ∩ (fun z => (g z, A z)) ⁻¹' {(0, A x)} := by
    ext z
    simp only [hF, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Prod.mk.injEq, hg, funext_iff, Pi.zero_apply]
    constructor
    · rintro ⟨hzb, h0, hzA⟩
      exact ⟨ball_subset_closedBall hzb, h0, hzA⟩
    · rintro ⟨hzb, h0, hzA⟩
      refine ⟨?_, h0, hzA⟩
      rcases (mem_closedBall.1 hzb).lt_or_eq with hlt | heq
      · exact mem_ball.2 hlt
      · exfalso
        have hzK : z ∈ K := ⟨mem_sphere.2 heq, by funext i; exact h0 i⟩
        apply hεsub (show A z ∈ ball (A w) ε by rw [funext hzA]; exact hxD)
        exact ⟨z, hzK, rfl⟩
  have hFc : IsCompact F := by
    rw [hFeq]
    refine (isCompact_closedBall w r).of_isClosed_subset ?_ Set.inter_subset_left
    exact (hgc.prodMk A.continuous.continuousOn).preimage_isClosed_of_isClosed isClosed_closedBall
      isClosed_singleton

  set n := Fintype.card σ
  let L : (σ → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin n => ℂ) (Fintype.equivFin σ)
  set U : Set (Fin n → ℂ) := L.symm ⁻¹' ball w r with hU
  set h : (Fin n → ℂ) → Fin (k + d) → ℂ :=
    fun v => Fin.append (fun i => f i (L.symm v)) (A (L.symm v)) with hh
  set y : Fin (k + d) → ℂ := Fin.append (0 : Fin k → ℂ) (A x) with hy
  have hUo : IsOpen U := isOpen_ball.preimage L.symm.continuous
  have hhd : DifferentiableOn ℂ h U := by
    refine differentiableOn_pi.2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · simp only [hh, Fin.append_left]
      exact ((hf i).differentiableOn.mono (ball_subset_closedBall.trans hBN)).comp
        L.symm.differentiable.differentiableOn (fun v hv => hv)
    · simp only [hh, Fin.append_right]
      exact ((differentiable_apply (𝕜 := ℂ) j).comp
        (A.differentiable.comp L.symm.differentiable)).differentiableOn
  have hfib : {v | v ∈ U ∧ h v = y} = L.symm ⁻¹' F := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hU, hF, hh, hy]
    constructor
    · rintro ⟨hv, he⟩
      refine ⟨hv, fun i => ?_, ?_⟩
      · simpa using congrFun he (Fin.castAdd d i)
      · funext j
        simpa using congrFun he (Fin.natAdd k j)
    · rintro ⟨hv, h0, hA⟩
      refine ⟨hv, funext fun j => ?_⟩
      refine Fin.addCases (fun i => ?_) (fun j => ?_) j
      · simp [h0 i]
      · simp [hA]
  have hfibc : IsCompact {v | v ∈ U ∧ h v = y} := by
    rw [hfib, ← L.image_eq_preimage_symm]
    exact hFc.image L.continuous
  have hFfin : F.Finite := by
    have h1 := (hFin n (k + d) U h y hUo hhd hfibc).image L.symm
    rwa [hfib, Set.image_preimage_eq _ L.symm.surjective] at h1

  refine ⟨ball w r \ (F \ {x}), ?_, ?_⟩
  · exact (isOpen_ball.sdiff (hFfin.sdiff).isClosed).mem_nhds ⟨hxB, fun hx => hx.2 rfl⟩
  rintro x' ⟨hx'X, hx'B, hx'F⟩ hx'A
  by_contra hne
  exact hx'F ⟨⟨hx'B, zerosX x' hx'X (hBN (ball_subset_closedBall hx'B)), hx'A⟩, hne⟩
end IsolatedFibreNear
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
