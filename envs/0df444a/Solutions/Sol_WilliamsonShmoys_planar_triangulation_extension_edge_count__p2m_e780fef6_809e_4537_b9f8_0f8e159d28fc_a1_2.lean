-- Prove2me | solution 2 for WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_e780fef6_809e_4537_b9f8_0f8e159d28fc_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:37:33.120319+00:00
-- url     : https://prove2.me/submissions/6b158500-1513-4117-991e-219e3602c676

import Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph_on

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.exists_triangulated_planar_supergraph_on G hG hV
