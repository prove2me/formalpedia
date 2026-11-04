-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_88aeae11_6627_4561_98a0_139448671fc8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:43:31.673195+00:00
-- url     : https://prove2.me/submissions/05ed69fa-8459-4d4a-87c8-4a40de2b4fac

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_has_triangulated_supergraph__p2m_dc457ca2_cc5d_4b3b_81b3_dc716865aa77_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_le_of_triangulated_supergraph__p2m_dc457ca2_cc5d_4b3b_81b3_dc716865aa77_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G)
    (hn : 3 ≤ Fintype.card V) :
    letI : DecidableRel G.Adj := dG
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  letI : DecidableRel G.Adj := dG
  obtain ⟨H, dH, hsub, hcard⟩ :=
    WilliamsonShmoys.planarDrawingOn_has_triangulated_supergraph__p2m_dc457ca2_cc5d_4b3b_81b3_dc716865aa77_a1
      G dG hG hn
  exact WilliamsonShmoys.edge_count_le_of_triangulated_supergraph__p2m_dc457ca2_cc5d_4b3b_81b3_dc716865aa77_a1
    G H dG dH hsub hcard