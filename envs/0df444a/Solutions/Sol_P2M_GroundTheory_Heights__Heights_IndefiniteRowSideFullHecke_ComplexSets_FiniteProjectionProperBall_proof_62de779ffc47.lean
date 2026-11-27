-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteProjectionProperBall_proof_62de779ffc47
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:58:17.478058+00:00
-- url     : https://prove2.me/submissions/e72b3bc0-7eff-47eb-a8df-afe193276bd1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionProperBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionProperBall

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
namespace FiniteProjectionProperBall
theorem _root_.solution : FiniteProjectionProperBall.Statement := by
  intro σ _ X w d A hX hiso U hU
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  obtain ⟨W, hW, hWiso⟩ := hiso
  have hmem : N ∩ U ∩ W ∈ 𝓝 w := Filter.inter_mem (Filter.inter_mem (hNo.mem_nhds hwN) hU) hW
  obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hmem
  have hBN : Metric.closedBall w ρ ⊆ N := fun x hx => (hball hx).1.1

  set C : Set (σ → ℂ) := Metric.closedBall w ρ ∩ (fun z i => f i z) ⁻¹' {0} with hCdef
  have hCX : ∀ x ∈ C, x ∈ X := by
    intro x hx
    have hxN := hBN hx.1
    have : x ∈ X ∩ N := by
      rw [hXN]
      refine ⟨hxN, fun i => ?_⟩
      have := congrFun (show (fun i => f i x) = 0 from hx.2) i
      simpa using this
    exact this.1
  have hXC : ∀ x ∈ X, x ∈ Metric.closedBall w ρ → x ∈ C := by
    intro x hxX hxB
    have : x ∈ {z | z ∈ N ∧ ∀ i, f i z = 0} := hXN ▸ ⟨hxX, hBN hxB⟩
    refine ⟨hxB, ?_⟩
    show (fun i => f i x) = 0
    funext i
    simpa using this.2 i
  have hCcl : IsClosed C := by
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ Metric.isClosed_closedBall isClosed_singleton
    exact continuousOn_pi.mpr fun i => ((hf i).continuousOn).mono hBN
  have hC : IsCompact C := (isCompact_closedBall w ρ).of_isClosed_subset hCcl Set.inter_subset_left

  set S : Set (σ → ℂ) := C ∩ Metric.sphere w ρ with hSdef
  have hS : IsCompact S := hC.inter_right Metric.isClosed_sphere
  have hT : IsCompact (A '' S) := hS.image A.continuous
  have hAw : A w ∉ A '' S := by
    rintro ⟨x, hxS, hxA⟩
    have hxw : x = w := hWiso x ⟨hCX x hxS.1, (hball hxS.1.1).2⟩ hxA
    have hd := hxS.2
    rw [hxw, Metric.mem_sphere, dist_self] at hd
    exact hρ.ne hd
  obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.mp hT.isClosed.isOpen_compl (A w) hAw
  refine ⟨ρ, hρ, r, hr, fun x hx => (hball (Metric.ball_subset_closedBall hx)).1.2, ?_⟩
  intro K hKr hK
  have heq : {x | x ∈ X ∩ Metric.ball w ρ ∧ A x ∈ K} = C ∩ A ⁻¹' K := by
    ext x
    constructor
    · rintro ⟨⟨hxX, hxB⟩, hxK⟩
      exact ⟨hXC x hxX (Metric.ball_subset_closedBall hxB), hxK⟩
    · rintro ⟨hxC, hxK⟩
      refine ⟨⟨hCX x hxC, ?_⟩, hxK⟩
      have hle : dist x w ≤ ρ := hxC.1
      rcases hle.lt_or_eq with hlt | heq
      · exact hlt
      · exact absurd ⟨x, ⟨hxC, heq⟩, rfl⟩ (hrT (hKr hxK))
  rw [heq]
  exact hC.inter_right (hK.isClosed.preimage A.continuous)
end FiniteProjectionProperBall
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
