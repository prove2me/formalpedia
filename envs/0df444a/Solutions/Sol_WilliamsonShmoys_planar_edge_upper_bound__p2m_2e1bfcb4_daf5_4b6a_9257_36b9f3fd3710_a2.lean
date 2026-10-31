-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_2e1bfcb4_daf5_4b6a_9257_36b9f3fd3710_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:30:44.95483+00:00
-- url     : https://prove2.me/submissions/f8fdb73f-45b1-4c46-9e74-e9a56159f8c9

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound G hG hCard
