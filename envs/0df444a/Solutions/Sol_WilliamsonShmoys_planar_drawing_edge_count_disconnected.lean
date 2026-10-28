-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_disconnected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:02:00.448662+00:00
-- url     : https://prove2.me/submissions/f5ea0f6d-29a4-4797-bda4-e9a54a979f58
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connect_components
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_connected

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : ¬ H.Connected) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hKdraw, hKconn⟩ :=
    WilliamsonShmoys.planar_drawing_connect_components H hV hH hconn
  exact hHK.trans
    (WilliamsonShmoys.planar_drawing_edge_count_connected K hV hKdraw hKconn)