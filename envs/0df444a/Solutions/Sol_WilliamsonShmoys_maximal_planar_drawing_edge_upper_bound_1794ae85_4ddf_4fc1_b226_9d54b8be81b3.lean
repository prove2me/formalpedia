-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_upper_bound_1794ae85_4ddf_4fc1_b226_9d54b8be81b3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T22:58:54.373347+00:00
-- url     : https://prove2.me/submissions/2713f956-6dff-4154-8008-cf7159d452d3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_1794ae85
import Theorems.Thm_WilliamsonShmoys_connected_planar_graph_edge_bound_1794ae85
import Theorems.Thm_WilliamsonShmoys_edge_count_mono_of_subgraph_1794ae85

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hHconn, hHD⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension_1794ae85 G hG hV
  exact le_trans
    (WilliamsonShmoys.edge_count_mono_of_subgraph_1794ae85 G H hGH)
    (WilliamsonShmoys.connected_planar_graph_edge_bound_1794ae85 H hHD hHconn hV)