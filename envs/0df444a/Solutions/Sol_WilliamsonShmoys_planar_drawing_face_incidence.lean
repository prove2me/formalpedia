-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_incidence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:40:16.932762+00:00
-- url     : https://prove2.me/submissions/8876d858-f822-4581-91f8-10cd3f9601bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_for_face_incidence

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V)
    (f : ℕ)
    (hEuler : K.edgeSet.ncard + 2 = Fintype.card V + f) :
    3 * f ≤ 2 * K.edgeSet.ncard := by
  have hEdge : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_drawing_edge_bound_for_face_incidence K hK hconn hV
  omega
