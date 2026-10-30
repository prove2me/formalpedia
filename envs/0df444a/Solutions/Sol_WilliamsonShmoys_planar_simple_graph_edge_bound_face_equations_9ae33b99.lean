-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound_face_equations_9ae33b99
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:34:46.957984+00:00
-- url     : https://prove2.me/submissions/ee05dd4f-3eac-4d95-9a6e-0cd942f84719

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_supergraph_9ae33b99
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_9ae33b99

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hsub, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_drawing_supergraph_9ae33b99 G hG
  have hcount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_9ae33b99 H hmax hCard
  exact le_trans (Set.ncard_mono hsub) (by rw [hcount])