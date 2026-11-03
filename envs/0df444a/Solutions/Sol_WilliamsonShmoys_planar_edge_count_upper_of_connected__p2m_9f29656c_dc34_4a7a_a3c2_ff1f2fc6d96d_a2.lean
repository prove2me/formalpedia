-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_of_connected__p2m_9f29656c_dc34_4a7a_a3c2_ff1f2fc6d96d_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:23:14.826207+00:00
-- url     : https://prove2.me/submissions/fa36800e-158a-4820-9c39-a71f385da727

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_84f2d88d_c1bb_48f4_b85d_8d668d11d624_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hConnectedBound :
      ∀ {W : Type} [Fintype W] [LinearOrder W] (K : SimpleGraph W),
        HasPlanarDrawingOn K → K.Connected →
        3 ≤ Fintype.card W →
        K.edgeSet.ncard + 6 ≤ 3 * Fintype.card W) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_84f2d88d_c1bb_48f4_b85d_8d668d11d624_a1 M hM hCard