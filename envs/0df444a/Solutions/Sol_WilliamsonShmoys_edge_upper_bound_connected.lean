-- Prove2me | solution 1 for WilliamsonShmoys.edge_upper_bound_connected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:26:18.755266+00:00
-- url     : https://prove2.me/submissions/cbb8ceb6-74df-4c0b-ad42-b17d2d5ab6cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_face_count_from_arcs_v4

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hConn : G.Connected)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V) :
    (G.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨f, heuler, hfaces⟩ :=
    WilliamsonShmoys.connected_drawing_euler_face_count_from_arcs_v4
      G hG hConn hCard
  omega