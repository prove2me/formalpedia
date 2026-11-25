-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_proper_projection_nbhd_b097f0104f75
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:06.460559+00:00
-- url     : https://prove2.me/submissions/911d9054-7df0-4e75-b4f8-7077094d8c9a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalParametrisation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermFiniteProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteGermProjectionCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalParametrisation

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ} {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (hX : IsAnalyticNear X w) (hw : w ∈ X)
    (hiso : ∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) {U : Set (σ → ℂ)} (hU : U ∈ 𝓝 w) :
    ∃ (B : Set (σ → ℂ)) (D : Set (Fin d → ℂ)), IsOpen B ∧ B ⊆ U ∧ w ∈ X ∩ B ∧ IsOpen D ∧
      IsPreconnected D ∧ Set.MapsTo A (X ∩ B) D ∧
      (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) ∧
      (∀ x ∈ X ∩ B, A x = A w → x = w) := by
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  obtain ⟨W, hW, hisoW⟩ := hiso
  obtain ⟨r₀, hr₀, hball⟩ :=
    Metric.mem_nhds_iff.1 (Filter.inter_mem (Filter.inter_mem hU (hNo.mem_nhds hwN)) hW)
  set r := r₀ / 2 with hr
  have hr0 : 0 < r := half_pos hr₀
  have hcb : Metric.closedBall w r ⊆ U ∩ N ∩ W :=
    (Metric.closedBall_subset_ball (half_lt_self hr₀)).trans hball

  set Z : Set (σ → ℂ) := Metric.closedBall w r ∩ ⋂ i, (Metric.closedBall w r ∩ f i ⁻¹' {0}) with hZ
  have hZc : IsClosed Z := by
    refine Metric.isClosed_closedBall.inter (isClosed_iInter fun i => ?_)
    exact ((hf i).continuousOn.mono fun z hz => (hcb hz).1.2).preimage_isClosed_of_isClosed
      Metric.isClosed_closedBall isClosed_singleton
  have hZk : IsCompact Z := (isCompact_closedBall w r).of_isClosed_subset hZc Set.inter_subset_left
  have hZX : ∀ z ∈ Metric.closedBall w r, (z ∈ X ↔ z ∈ Z) := by
    intro z hz
    have hzN : z ∈ N := (hcb hz).1.2
    constructor
    · intro hzX
      have h1 : z ∈ X ∩ N := ⟨hzX, hzN⟩
      rw [hXN] at h1
      exact ⟨hz, Set.mem_iInter.2 fun i => ⟨hz, h1.2 i⟩⟩
    · intro hzZ
      have h2 : z ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := ⟨hzN, fun i => (Set.mem_iInter.1 hzZ.2 i).2⟩
      rw [← hXN] at h2
      exact h2.1

  have hSk : IsCompact (Z ∩ Metric.sphere w r) := hZk.inter_right Metric.isClosed_sphere
  have hAS : A w ∉ A '' (Z ∩ Metric.sphere w r) := by
    rintro ⟨x, ⟨hxZ, hxs⟩, hxA⟩
    have hxcb : x ∈ Metric.closedBall w r := Metric.sphere_subset_closedBall hxs
    have hxw := hisoW x ⟨(hZX x hxcb).2 hxZ, (hcb hxcb).2⟩ hxA
    rw [hxw, Metric.mem_sphere, dist_self] at hxs
    exact hr0.ne hxs
  obtain ⟨ε, hε, hεS⟩ :=
    Metric.mem_nhds_iff.1 ((hSk.image A.continuous).isClosed.isOpen_compl.mem_nhds hAS)
  refine ⟨Metric.ball w r ∩ A ⁻¹' Metric.ball (A w) ε, Metric.ball (A w) ε,
    Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage A.continuous), ?_,
    ⟨hw, Metric.mem_ball_self hr0, Metric.mem_ball_self hε⟩, Metric.isOpen_ball,
    (convex_ball _ _).isPreconnected, fun x hx => hx.2.2, ?_, ?_⟩
  · exact fun x hx => (hcb (Metric.ball_subset_closedBall hx.1)).1.1
  · intro K hKD hK
    have heq : {x | x ∈ X ∩ (Metric.ball w r ∩ A ⁻¹' Metric.ball (A w) ε) ∧ A x ∈ K} =
        Z ∩ A ⁻¹' K := by
      ext x
      constructor
      · rintro ⟨⟨hxX, hxb, -⟩, hxK⟩
        exact ⟨(hZX x (Metric.ball_subset_closedBall hxb)).1 hxX, hxK⟩
      · rintro ⟨hxZ, hxK⟩
        have hxcb : x ∈ Metric.closedBall w r := hxZ.1
        refine ⟨⟨(hZX x hxcb).2 hxZ, ?_, hKD hxK⟩, hxK⟩
        by_contra hxb
        have hxs : x ∈ Metric.sphere w r :=
          Metric.mem_sphere.2 (le_antisymm (Metric.mem_closedBall.1 hxcb)
            (not_lt.1 fun h => hxb (Metric.mem_ball.2 h)))
        exact hεS (hKD hxK) ⟨x, ⟨hxZ, hxs⟩, rfl⟩
    rw [heq]
    exact hZk.inter_right (hK.isClosed.preimage A.continuous)
  · exact fun x hx hxA => hisoW x ⟨hx.1, (hcb (Metric.ball_subset_closedBall hx.2.1)).2⟩ hxA
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
