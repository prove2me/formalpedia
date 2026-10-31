-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper__p2m_36d62909_fefb_443f_ad8e_654ce0b0b7dd_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:52:38.864772+00:00
-- url     : https://prove2.me/submissions/22e697fa-018a-4079-9cb8-f0f4b8d6dfa7

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound K hK hV
