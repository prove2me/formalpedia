-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_bound_of_connected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:55:14.095095+00:00
-- url     : https://prove2.me/submissions/ff26907e-9765-4f4b-a423-68c9d3b2a44c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_certificate_17d80af8_466c_425b_8fbb_a9c22e363e50

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) (hcard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, heuler, hface⟩ :=
    WilliamsonShmoys.planar_drawing_edge_count_certificate_17d80af8_466c_425b_8fbb_a9c22e363e50
      H hH hconn hcard
  omega