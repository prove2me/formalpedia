-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_69a4b515_b2d1_4c44_a03e_fe4ffa3a8acf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:42:44.646897+00:00
-- url     : https://prove2.me/submissions/1ff5522d-5a0b-407c-97fe-53eb37d19256

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_triangulation_edge_count

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N ≤ P →
      WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_edge_count N hV hN hmax
