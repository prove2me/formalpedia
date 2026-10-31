-- Prove2me | solution 2 for WilliamsonShmoys.planar_triangulation_completion_edge_count__p2m_b7ddd4a0_5822_4de2_a826_6e2dd80a911f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:46:33.258983+00:00
-- url     : https://prove2.me/submissions/c510c5a4-67e4-4f8f-b7d6-61551949c193

import Theorems.Thm_WilliamsonShmoys_planar_graph_has_dense_supergraph_completion

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_graph_has_dense_supergraph_completion G hCard hG
