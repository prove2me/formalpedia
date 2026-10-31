-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_718d0665_f14e_4e4a_9ebf_3d91778b5251_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:57:07.187696+00:00
-- url     : https://prove2.me/submissions/6dfe24e3-cd6e-4213-a833-822e7312dfc6

import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_for_triangulation_exact_edge_count

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V,
      N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N) :
    3 * Fintype.card V - 6 = N.edgeSet.ncard :=
  WilliamsonShmoys.edge_count_of_maximal_planar_drawing_for_triangulation_exact_edge_count N hV hN hmax
