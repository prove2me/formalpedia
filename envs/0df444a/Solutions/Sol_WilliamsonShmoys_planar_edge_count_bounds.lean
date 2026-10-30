-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:37:40.451614+00:00
-- url     : https://prove2.me/submissions/4b4c85be-edb3-4132-b780-75e155384f27

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_lower_88511758
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_88511758

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Fintype.card V ≤ H.edgeSet.ncard + 1 ∧
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  exact ⟨WilliamsonShmoys.planar_edge_count_lower_88511758 H hconn,
    WilliamsonShmoys.planar_drawing_edge_count_upper_88511758 H hV hconn hH⟩