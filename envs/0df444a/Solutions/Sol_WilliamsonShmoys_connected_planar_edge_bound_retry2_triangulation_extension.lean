-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound_retry2_triangulation_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:22:44.495975+00:00
-- url     : https://prove2.me/submissions/559b3c97-060e-48eb-9e2a-1d8d05cb20cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_same_vertices_retry2_triangulation_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_retry2_triangulation_extension
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 <= Fintype.card V) :
    Exists fun H : SimpleGraph V =>
      G <= H /\
      WilliamsonShmoys.HasPlanarDrawingOn H /\
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHDraw, hHConn, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_same_vertices_retry2_triangulation_extension
      G hDraw hConn
  have hCount := WilliamsonShmoys.maximal_planar_edge_count_retry2_triangulation_extension
    H hHDraw hHConn hCard hMax
  exact ⟨H, hGH, hHDraw, hCount⟩