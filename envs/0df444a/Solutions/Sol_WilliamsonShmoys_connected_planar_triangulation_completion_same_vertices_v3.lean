-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_triangulation_completion_same_vertices_v3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:39:34.887632+00:00
-- url     : https://prove2.me/submissions/07ffe696-07a8-4f43-8437-3445f68b6054
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_maximal_supergraph_same_vertices
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_e5e61a9e_aae6_41b6_82c4_d73ea4490ad9

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hKdraw, hKconn, hKmax⟩ :=
    WilliamsonShmoys.connected_planar_maximal_supergraph_same_vertices
      H hdraw hconn
  refine ⟨K, hHK, hKdraw, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_edge_count_e5e61a9e_aae6_41b6_82c4_d73ea4490ad9
    K hV hKdraw hKconn hKmax