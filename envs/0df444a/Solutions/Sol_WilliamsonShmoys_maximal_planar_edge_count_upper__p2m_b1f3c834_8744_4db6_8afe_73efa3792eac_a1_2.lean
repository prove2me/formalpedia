-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_b1f3c834_8744_4db6_8afe_73efa3792eac_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:02:48.678638+00:00
-- url     : https://prove2.me/submissions/8da18226-8df7-4bee-896f-f46b6c75c735

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V) (hDraw : HasPlanarDrawingOn P) (hV : 3 ≤ Fintype.card V) : P.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound P hDraw hV
