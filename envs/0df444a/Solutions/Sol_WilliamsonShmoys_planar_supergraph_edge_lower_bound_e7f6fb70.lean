-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_lower_bound_e7f6fb70
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:29:09.983314+00:00
-- url     : https://prove2.me/submissions/f23ad6b8-5275-4980-aee5-a9d9402faadf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_e7f6fb70
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_lower_bound_e7f6fb70

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    exists Z : SimpleGraph V,
      Y <= Z /\ WilliamsonShmoys.HasPlanarDrawingOn Z /\
        3 * Fintype.card V <= Z.edgeSet.ncard + 6 := by
  obtain ⟨Z, hYZ, hZ, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph_e7f6fb70 Y hY
  exact ⟨Z, hYZ, hZ,
    WilliamsonShmoys.maximal_planar_graph_edge_lower_bound_e7f6fb70 Z hV hZ hmax⟩