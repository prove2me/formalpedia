-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_c00979a8_planar_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:30:03.150072+00:00
-- url     : https://prove2.me/submissions/f35e856f-2014-4fd7-8ac9-e48427c752a1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_c00979a8
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_c00979a8

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hKH, hconn, hdraw, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph_c00979a8 K hK
  have hbound :=
    WilliamsonShmoys.connected_planar_edge_bound_c00979a8 H hV hconn hdraw
  omega