-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_719d44f8_6785_426b_9f1b_0bb1d58add17
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:46:41.753809+00:00
-- url     : https://prove2.me/submissions/818cb8aa-ce9e-43cc-9aa7-ea053a38c9d1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_on_same_vertices_for_edge_bound_719d44f8
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_for_edge_bound_719d44f8

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    P.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hPH, hH, hmax, hcard_le⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_on_same_vertices_for_edge_bound_719d44f8 P hV hP
  have hcard_eq :=
    WilliamsonShmoys.maximal_planar_graph_edge_count_for_edge_bound_719d44f8 H hV hH hmax
  omega