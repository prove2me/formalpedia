-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_9bfb6b72_08dc_4057_9f94_78efbb45a4ca_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:24:40.058393+00:00
-- url     : https://prove2.me/submissions/35c1d797-0e82-4ccb-8e28-6d8099f3a513
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_d16397ab_f97b_4b48_8e65_cb91b43850d6_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_d16397ab_f97b_4b48_8e65_cb91b43850d6_a1
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ H' : SimpleGraph V, H ≤ H' → HasPlanarDrawingOn H' → H' = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hup := WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_d16397ab_f97b_4b48_8e65_cb91b43850d6_a1 H hH hV
  have hlo := WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_d16397ab_f97b_4b48_8e65_cb91b43850d6_a1 H hH hV hmax
  omega