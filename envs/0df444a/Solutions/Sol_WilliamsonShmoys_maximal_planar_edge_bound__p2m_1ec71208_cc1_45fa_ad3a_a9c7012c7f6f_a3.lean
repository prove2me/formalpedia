-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_1ec71208_cc1_45fa_ad3a_a9c7012c7f6f_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:10:59.681232+00:00
-- url     : https://prove2.me/submissions/ef3eaa84-5f11-497a-812b-8aaa39daf7ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_fd310935_5091_4856_a806_c268ac2a777f_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  exact WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_fd310935_5091_4856_a806_c268ac2a777f_a1
    H hcard hdraw