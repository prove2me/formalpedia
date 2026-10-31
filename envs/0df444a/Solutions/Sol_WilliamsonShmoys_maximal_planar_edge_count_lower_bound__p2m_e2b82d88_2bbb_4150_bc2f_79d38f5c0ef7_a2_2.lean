-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_e2b82d88_2bbb_4150_bc2f_79d38f5c0ef7_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:27:10.076219+00:00
-- url     : https://prove2.me/submissions/cca5896c-09d4-4f57-8e96-5b73ffbd1167

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound_06232b3e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    3 * Fintype.card V - 6 ≤ N.edgeSet.ncard :=
  WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_06232b3e N hN hCard hMax
