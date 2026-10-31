-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_2cc4f687_238d_40a3_a706_2eb34249ae45_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:43:59.86206+00:00
-- url     : https://prove2.me/submissions/cc171eb8-b9c8-4dd4-a1bc-308524b8728a

import Theorems.Thm_WilliamsonShmoys_planar_triangulated_extension_maximal_supergraph_edge_count

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : forall K : SimpleGraph V, H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_triangulated_extension_maximal_supergraph_edge_count H hCard hH hMax
