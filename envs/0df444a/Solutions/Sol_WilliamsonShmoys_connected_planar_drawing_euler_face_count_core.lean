-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler_face_count_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T01:04:10.862335+00:00
-- url     : https://prove2.me/submissions/db1d8be5-54c2-43c5-9631-b691e4855ca3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_count_core_euler
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_count_core_boundary

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : L.Connected)
    (hdraw : HasPlanarDrawingOn L) :
    ∃ f : ℕ, 3 * f ≤ 2 * L.edgeSet.ncard ∧
      Fintype.card V + f = L.edgeSet.ncard + 2 := by
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.connected_planar_drawing_euler_face_count_core_euler
      L hV hconn hdraw
  exact ⟨f,
    WilliamsonShmoys.connected_planar_drawing_euler_face_count_core_boundary
      L hV hconn hdraw f heuler,
    heuler⟩