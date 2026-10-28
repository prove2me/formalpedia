-- Prove2me | solution 1 for WilliamsonShmoys.connected_drawing_euler_bound_retry3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T21:47:50.321984+00:00
-- url     : https://prove2.me/submissions/e13ab15b-dc7d-4874-8775-a490351f4f75
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_drawing_has_euler_face_count

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, heuler, hface⟩ :=
    WilliamsonShmoys.connected_drawing_has_euler_face_count
      G hconn hdraw hcard
  omega