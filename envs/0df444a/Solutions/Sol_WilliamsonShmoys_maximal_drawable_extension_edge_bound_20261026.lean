-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_extension_edge_bound_20261026
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:00:07.825328+00:00
-- url     : https://prove2.me/submissions/7e57c1f8-d310-4132-a361-6d2947c647c9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_on_same_vertices
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hLH, hH, hMax, hLE⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_on_same_vertices L hL hV
  have hEdges := WilliamsonShmoys.maximal_planar_graph_edge_count H hH hV hMax
  exact le_trans hLE (le_of_eq hEdges)