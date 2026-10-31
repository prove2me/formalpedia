-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_8d45bf42_38ea_432e_b84b_d41270aef8ba_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:30:26.112925+00:00
-- url     : https://prove2.me/submissions/46a7e7a3-ddf9-42b5-8988-d1765160d1ae

import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count__p2m_397071d2_54cd_4807_97e7_b4001b0535bd_a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H) (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) : H.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.edge_maximal_planar_edge_count__p2m_397071d2_54cd_4807_97e7_b4001b0535bd_a2 H hV hH hmax
