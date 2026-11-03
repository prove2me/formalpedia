-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_from_connected_components__p2m_c46714b6_9bfd_40bf_95c8_08d778b86369_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T16:11:27.468179+00:00
-- url     : https://prove2.me/submissions/a2860f45-f1ff-4b1d-9826-ca3713ded5dc

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn H)
    (hconn : ∀ (W : Type) [Fintype W] [LinearOrder W] (K : SimpleGraph W),
      3 ≤ Fintype.card W → K.Connected → HasPlanarDrawingOn K →
      K.edgeSet.ncard + 6 ≤ 3 * Fintype.card W) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  exact WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound H hplanar hcard
