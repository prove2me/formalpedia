-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_6a6f73b1_aafd_4ec3_b910_d68356c6d6db_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:12:17.275656+00:00
-- url     : https://prove2.me/submissions/1259b329-51a5-49d7-ae38-d4170c2333f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_simple_planar_drawing_edge_bound__p2m_e4c5d8ab_7595_4333_b2f6_7c0fac6762c1_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = G)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := Classical.decRel _
     G.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  exact WilliamsonShmoys.simple_planar_drawing_edge_bound__p2m_e4c5d8ab_7595_4333_b2f6_7c0fac6762c1_a2 G hG hcard