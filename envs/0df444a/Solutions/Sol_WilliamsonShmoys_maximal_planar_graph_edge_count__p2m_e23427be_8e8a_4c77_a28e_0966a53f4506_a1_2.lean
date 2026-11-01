-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_e23427be_8e8a_4c77_a28e_0966a53f4506_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:17:37.451372+00:00
-- url     : https://prove2.me/submissions/14ac5843-8541-4c8c-a876-750d8a90bb6b

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_eq_from_drawing__p2m_cf5b9138_9b5a_4508_a5f4_a698107874c7_a1
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hHmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.maximal_planar_edge_count_eq_from_drawing__p2m_cf5b9138_9b5a_4508_a5f4_a698107874c7_a1 H hH hV hHmax
