-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_exact_edge_count_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:12:27.102935+00:00
-- url     : https://prove2.me/submissions/c723d363-0d44-4b35-b384-95c1d5fd79b2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_exists_v3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count_v3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hKH, hDraw, hCount, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph_exists_v3 K hK
  have hExact :=
    WilliamsonShmoys.maximal_planar_drawing_exact_edge_count_v3 H hDraw hCard hMax
  omega