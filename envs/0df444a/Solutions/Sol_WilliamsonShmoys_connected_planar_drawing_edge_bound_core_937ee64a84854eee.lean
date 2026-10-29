-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_bound_core_937ee64a84854eee
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:48:57.277488+00:00
-- url     : https://prove2.me/submissions/dbc05938-7050-48bf-9f9f-7e010da5fc2d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_count_core

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : L.Connected)
    (hdraw : HasPlanarDrawingOn L) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hfaces, heuler⟩ :=
    WilliamsonShmoys.connected_planar_drawing_euler_face_count_core
      L hV hconn hdraw
  omega