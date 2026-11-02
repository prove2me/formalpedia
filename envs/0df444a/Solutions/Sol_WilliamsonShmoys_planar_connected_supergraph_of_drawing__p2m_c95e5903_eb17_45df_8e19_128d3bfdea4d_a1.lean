-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_supergraph_of_drawing__p2m_c95e5903_eb17_45df_8e19_128d3bfdea4d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:53:24.983227+00:00
-- url     : https://prove2.me/submissions/972781bd-ee33-4776-bda0-56b5c79371af
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_across_components__p2m_e04f1e17_20de_446c_b9b1_9c0568158af1_a1
import Theorems.Thm_WilliamsonShmoys_planar_connected_extension_from_bridge_steps__p2m_e04f1e17_20de_446c_b9b1_9c0568158af1_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hne : 0 < Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        (letI : DecidableRel G.Adj := Classical.decRel G.Adj
         letI : DecidableRel H.Adj := Classical.decRel H.Adj
         G.edgeFinset.card ≤ H.edgeFinset.card) := by
  apply WilliamsonShmoys.planar_connected_extension_from_bridge_steps__p2m_e04f1e17_20de_446c_b9b1_9c0568158af1_a1
      G hG hne
  intro K hGK hK hKnot
  classical
  rw [SimpleGraph.connected_iff_exists_forall_reachable] at hKnot
  push_neg at hKnot
  haveI : Nonempty V := Fintype.card_pos_iff.mp hne
  obtain ⟨u⟩ := ‹Nonempty V›
  obtain ⟨v, huv⟩ := hKnot u
  obtain ⟨L, hKL, hLadj, hLplanar⟩ :=
    WilliamsonShmoys.planar_drawing_add_edge_across_components__p2m_e04f1e17_20de_446c_b9b1_9c0568158af1_a1
      K hK u v huv
  exact ⟨L, hKL, hLplanar, u, v, huv, hLadj⟩
