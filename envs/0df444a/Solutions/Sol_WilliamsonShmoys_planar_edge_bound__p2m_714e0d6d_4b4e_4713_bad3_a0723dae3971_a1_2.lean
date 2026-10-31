-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_bound__p2m_714e0d6d_4b4e_4713_bad3_a0723dae3971_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T20:58:24.862836+00:00
-- url     : https://prove2.me/submissions/2702eef6-010a-45e9-ac56-a484769e7b0c

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_three_or_more_vertices_connected_core

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_bound_for_three_or_more_vertices_connected_core H hplanar hconnected hV
