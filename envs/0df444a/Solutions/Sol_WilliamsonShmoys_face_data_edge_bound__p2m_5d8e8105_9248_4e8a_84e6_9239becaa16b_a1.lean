-- Prove2me | solution 1 for WilliamsonShmoys.face_data_edge_bound__p2m_5d8e8105_9248_4e8a_84e6_9239becaa16b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:17:17.315838+00:00
-- url     : https://prove2.me/submissions/d05a319a-edfa-434e-a4d9-9dcb9b12e3d6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (F B : Nat)
    (hEuler : Fintype.card V + F = K.edgeFinset.card + 2)
    (hBoundaryLower : 3 * F <= B)
    (hBoundaryCount : B = 2 * K.edgeFinset.card) :
    K.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  omega