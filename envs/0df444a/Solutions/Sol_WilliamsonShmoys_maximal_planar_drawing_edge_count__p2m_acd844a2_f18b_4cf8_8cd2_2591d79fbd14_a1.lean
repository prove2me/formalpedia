-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_acd844a2_f18b_4cf8_8cd2_2591d79fbd14_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:36:06.937827+00:00
-- url     : https://prove2.me/submissions/65671c7a-81c7-4768-b318-de7e01924b2c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_21c82e8b_ea63_4b29_98bb_ab69d1fee3ec_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_21c82e8b_ea63_4b29_98bb_ab69d1fee3ec_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hu := WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_21c82e8b_ea63_4b29_98bb_ab69d1fee3ec_a1
    H hcard hH
  have hl := WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_21c82e8b_ea63_4b29_98bb_ab69d1fee3ec_a1
    H hcard hH hmax
  omega