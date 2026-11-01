-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_c643eab9_16cc_4e69_8d73_dd1e68fa5bd2_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:20:44.892813+00:00
-- url     : https://prove2.me/submissions/6fef21c2-4bbc-414d-968b-3d78be4ab32b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_710ae9cd_06e1_4ca5_a820_3c02fa6bdb35_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, HasPlanarDrawingOn K →
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       letI : DecidableRel K.Adj := Classical.decRel K.Adj
       H.edgeFinset ⊆ K.edgeFinset → K.edgeFinset ⊆ H.edgeFinset))
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  exact WilliamsonShmoys.planar_drawing_edge_bound__p2m_710ae9cd_06e1_4ca5_a820_3c02fa6bdb35_a1 H hH hcard