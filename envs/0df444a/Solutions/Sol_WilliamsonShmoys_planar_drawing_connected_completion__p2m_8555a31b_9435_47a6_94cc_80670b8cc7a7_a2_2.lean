-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_completion__p2m_8555a31b_9435_47a6_94cc_80670b8cc7a7_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:35:55.662332+00:00
-- url     : https://prove2.me/submissions/b455653a-fe45-41b4-870d-a407e4208153

import Theorems.Thm_WilliamsonShmoys_connect_planar_drawing__p2m_52d80640_fd16_42f7_b63d_2010f98eda2f_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H :=
  WilliamsonShmoys.connect_planar_drawing__p2m_52d80640_fd16_42f7_b63d_2010f98eda2f_a1 K hcard hK