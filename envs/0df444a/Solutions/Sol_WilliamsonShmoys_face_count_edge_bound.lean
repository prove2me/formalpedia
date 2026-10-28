-- Prove2me | solution 1 for WilliamsonShmoys.face_count_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:39:01.524978+00:00
-- url     : https://prove2.me/submissions/c30e92cf-01fb-4504-a26f-f625f8050647

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V)
    (f : ℕ)
    (heuler : K.edgeSet.ncard + 2 = Fintype.card V + f)
    (hfaces : 3 * f ≤ 2 * K.edgeSet.ncard) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  omega