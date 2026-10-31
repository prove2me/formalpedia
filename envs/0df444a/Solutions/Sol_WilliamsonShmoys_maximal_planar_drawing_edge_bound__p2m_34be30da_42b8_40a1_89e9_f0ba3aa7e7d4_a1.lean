-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_34be30da_42b8_40a1_89e9_f0ba3aa7e7d4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:39:25.917584+00:00
-- url     : https://prove2.me/submissions/def72af1-ad10-48f1-87d1-a00f4ee5ff6a

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound_06232b3e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hCard : 3 ≤ Fintype.card V) (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) : 3 * Fintype.card V - 6 ≤ H.edgeSet.ncard :=
  WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_06232b3e H hH hCard hmax
