-- Prove2me | solution 3 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_71827a3a_7db4_46f3_80ab_2c37e012e77b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:14:35.426556+00:00
-- url     : https://prove2.me/submissions/8625df38-4c0b-400c-8977-4692ec19efc8

import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound__p2m_bdf730fd_a18a_4f08_870b_a5969b01342b_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_simple_edge_bound__p2m_bdf730fd_a18a_4f08_870b_a5969b01342b_a1 M hcard hplanar
