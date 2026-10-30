-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler_edge_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:44:01.70364+00:00
-- url     : https://prove2.me/submissions/a52e080f-05e3-42fd-b541-001db25b03e5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_edge_bound_v2_planar_completion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hprops⟩ :=
    WilliamsonShmoys.connected_planar_drawing_euler_edge_bound_v2_planar_completion
      K hV hK hconn
  calc
    K.edgeSet.ncard ≤ H.edgeSet.ncard := hprops.2.2.1
    _ = 3 * Fintype.card V - 6 := hprops.2.2.2