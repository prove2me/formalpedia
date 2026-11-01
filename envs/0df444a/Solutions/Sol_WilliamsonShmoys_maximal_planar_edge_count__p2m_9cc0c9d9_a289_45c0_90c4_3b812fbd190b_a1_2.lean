-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_9cc0c9d9_a289_45c0_90c4_3b812fbd190b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:21:12.895599+00:00
-- url     : https://prove2.me/submissions/a6f453af-402a-4d2b-ba4f-cb2af2712ab5

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_9fdf65a3_2cbf_4cec_9951_ee8b977e74bf_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      Set.Subset M.edgeSet N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_9fdf65a3_2cbf_4cec_9951_ee8b977e74bf_a1 M hM hV hmax
