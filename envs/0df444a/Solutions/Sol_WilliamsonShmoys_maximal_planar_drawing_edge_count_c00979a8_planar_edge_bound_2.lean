-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_edge_count_c00979a8_planar_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:02:49.487011+00:00
-- url     : https://prove2.me/submissions/eb71cbf5-abcb-4d33-96e2-0e5a1bfa5a0b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_ge3_c00979a8
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_c00979a8

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hKH, hconn, hdraw, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph_ge3_c00979a8
      K hV hK
  have hbound :=
    WilliamsonShmoys.connected_planar_edge_bound_c00979a8 H hV hconn hdraw
  omega