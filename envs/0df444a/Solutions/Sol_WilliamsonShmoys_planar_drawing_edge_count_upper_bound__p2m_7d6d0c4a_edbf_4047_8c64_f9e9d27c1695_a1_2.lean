-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_7d6d0c4a_edbf_4047_8c64_f9e9d27c1695_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:11:46.162806+00:00
-- url     : https://prove2.me/submissions/d7606a35-3a88-4069-9543-6808e5f74434

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_retry3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 <= Fintype.card V) : G.edgeSet.ncard <= 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_edge_count_bound_retry3 G hDraw hV
