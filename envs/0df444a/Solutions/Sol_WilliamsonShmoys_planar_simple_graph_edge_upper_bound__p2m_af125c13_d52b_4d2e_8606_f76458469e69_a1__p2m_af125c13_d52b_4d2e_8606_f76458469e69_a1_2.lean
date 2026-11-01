-- Prove2me | solution 2 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1__p2m_af125c13_d52b_4d2e_8606_f76458469e69_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:14:10.042186+00:00
-- url     : https://prove2.me/submissions/74b04110-f740-46a3-a0ed-c23e4f224ebc

import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound__p2m_bdf730fd_a18a_4f08_870b_a5969b01342b_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_simple_edge_bound__p2m_bdf730fd_a18a_4f08_870b_a5969b01342b_a1 M hcard hplanar
