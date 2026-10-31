-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_9715dea8_fcd2_44d6_b5ec_a796b1fa76e9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:50:17.627999+00:00
-- url     : https://prove2.me/submissions/8e2ac6f5-2405-4de5-8f4a-9e1797f5f523

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound_for_triangulation_1e14dc85_fe67_4e30_934e_c619828dd605

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_drawing_edge_bound_for_triangulation_1e14dc85_fe67_4e30_934e_c619828dd605 M hM hCard hMax
