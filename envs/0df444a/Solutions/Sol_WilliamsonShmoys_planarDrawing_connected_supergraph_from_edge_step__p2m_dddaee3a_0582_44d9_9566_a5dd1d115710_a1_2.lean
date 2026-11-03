-- Prove2me | solution 2 for WilliamsonShmoys.planarDrawing_connected_supergraph_from_edge_step__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:50:31.035328+00:00
-- url     : https://prove2.me/submissions/51470ff4-3952-4772-b4c6-b80957c2cd74

import Theorems.Thm_WilliamsonShmoys_connect_planar_drawing__p2m_52d80640_fd16_42f7_b63d_2010f98eda2f_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hn : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hstep : ∀ G : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn G →
      ¬ G.Connected →
      ∃ u v : V, ¬ G.Reachable u v ∧
        ∃ H : SimpleGraph V,
          G ≤ H ∧
          H.edgeSet = G.edgeSet ∪ {Sym2.mk u v} ∧
          WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H :=
  WilliamsonShmoys.connect_planar_drawing__p2m_52d80640_fd16_42f7_b63d_2010f98eda2f_a1 K hn hK