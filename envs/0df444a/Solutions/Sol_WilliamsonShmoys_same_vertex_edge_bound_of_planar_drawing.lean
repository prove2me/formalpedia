-- Prove2me | solution 1 for WilliamsonShmoys.same_vertex_edge_bound_of_planar_drawing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:39:44.180861+00:00
-- url     : https://prove2.me/submissions/c2afa6af-776c-4f73-b53a-4cb57105291f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_extension_same_vertices
import Theorems.Thm_WilliamsonShmoys_edge_bound_for_maximal_planar_drawing

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.edge_maximal_planar_extension_same_vertices G hV hG
  have hbound :=
    WilliamsonShmoys.edge_bound_for_maximal_planar_drawing H hV hH hmax
  exact hGH.trans hbound