-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_301f4675_a625_4f03_8421_053f86d64c99_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:31:33.525395+00:00
-- url     : https://prove2.me/submissions/1fc80450-0599-4c52-9de7-9f07626e4256

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_upper_bound__p2m_7e36ab91_a082_401a_9ddf_0fa0bcba787f_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_7e36ab91_a082_401a_9ddf_0fa0bcba787f_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G) :
    3 * Fintype.card V = G.edgeSet.ncard + 6 := by
  have hupper := WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_7e36ab91_a082_401a_9ddf_0fa0bcba787f_a1
    G hV hG
  have hlower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7e36ab91_a082_401a_9ddf_0fa0bcba787f_a1
    G hV hG hmax
  omega