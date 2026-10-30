-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_connected
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:04:52.101482+00:00
-- url     : https://prove2.me/submissions/bba8f4c9-a8dd-41dd-8497-42d0b5751f99

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_same_vertices

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, hsub, hK, hcount, hmono⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_same_vertices H hV hH hconn
  omega