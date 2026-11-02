-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_augmentation__p2m_f36d5627_b6e6_48ed_8d0d_9e5de579a76e_a1__p2m_f36d5627_b6e6_48ed_8d0d_9e5de579a76e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:24:44.58624+00:00
-- url     : https://prove2.me/submissions/ea04c8cc-1b32-4720-9df6-483514d92195

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (instH : DecidableRel H.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ u v, K.Adj u v → H.Adj u v) ∧
      (∀ (G' : SimpleGraph V), WilliamsonShmoys.HasPlanarDrawingOn G' →
        (∀ u v, H.Adj u v → G'.Adj u v) →
        (∀ u v, G'.Adj u v → H.Adj u v)) ∧
      (letI : DecidableRel H.Adj := instH; K.edgeFinset.card ≤ H.edgeFinset.card) := by
  classical
  let p : SimpleGraph V → Prop := fun G =>
    WilliamsonShmoys.HasPlanarDrawingOn G ∧ K ≤ G
  have hp : ∃ G : SimpleGraph V, p G := by
    exact ⟨K, hK, le_rfl⟩
  obtain ⟨H, instH, hmax⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists p).mpr hp
  have hKH : K ≤ H := hmax.1.2
  refine ⟨H, instH, hmax.1.1, ?_, ?_, ?_⟩
  · intro u v huv
    exact hKH huv
  · intro G' hG' hHG'
    have hHG : H ≤ G' := hHG'
    have hKG' : K ≤ G' := le_trans hKH hHG
    have hcard : G'.edgeFinset.card ≤ H.edgeFinset.card :=
      hmax.2 ⟨hG', hKG'⟩
    have hgraph : H = G' := by
      apply SimpleGraph.edgeFinset_inj.mp
      exact Finset.eq_of_subset_of_card_le
        (SimpleGraph.edgeFinset_mono hHG) hcard
    intro u v huv
    rw [← hgraph] at huv
    exact huv
  · exact hmax.2 ⟨hK, le_rfl⟩