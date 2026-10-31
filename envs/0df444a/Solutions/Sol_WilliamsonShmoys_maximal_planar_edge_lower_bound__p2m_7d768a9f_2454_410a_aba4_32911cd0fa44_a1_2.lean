-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7d768a9f_2454_410a_aba4_32911cd0fa44_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:39:36.102972+00:00
-- url     : https://prove2.me/submissions/4fe0134a-cf6e-42f5-aa95-d8e2be0fdb90

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_triangulation_extension_20261026_maximal_planar_edge_count_lower_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ H.edgeSet.ncard :=
  WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_extension_20261026_maximal_planar_edge_count_lower_bound H hH hmax hV
