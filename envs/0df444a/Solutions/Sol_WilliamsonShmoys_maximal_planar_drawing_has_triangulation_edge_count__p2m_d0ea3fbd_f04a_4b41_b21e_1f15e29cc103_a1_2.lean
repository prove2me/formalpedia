-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_has_triangulation_edge_count__p2m_d0ea3fbd_f04a_4b41_b21e_1f15e29cc103_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:22:40.503429+00:00
-- url     : https://prove2.me/submissions/b84394e5-65e6-418b-8303-bcd663eb24da

import Theorems.Thm_WilliamsonShmoys_edge_count_of_edge_maximal_drawable_graph

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

/-- Euler's formula and triangular faces give the edge count for an inclusion-maximal planar graph. -/

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 <= Fintype.card V) (hMax : forall K : SimpleGraph V, G <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = G) : G.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.edge_count_of_edge_maximal_drawable_graph G hDraw hV hMax
