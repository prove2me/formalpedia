-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_05b91864_4011_4912_8401_09994d13f3f6_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:41:34.460427+00:00
-- url     : https://prove2.me/submissions/d77445bb-bfee-410e-843d-44e4c7c56efc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_connected__p2m_7237be62_bb2d_4386_ba18_ecdd0c420d72_a1
import Theorems.Thm_WilliamsonShmoys_connected_maximal_drawable_graph_edge_count__p2m_7237be62_bb2d_4386_ba18_ecdd0c420d72_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P = N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     N.edgeFinset.card = 3 * Fintype.card V - 6) := by
  have hconn : N.Connected :=
    WilliamsonShmoys.maximal_drawable_graph_connected__p2m_7237be62_bb2d_4386_ba18_ecdd0c420d72_a1
      N hcard hN hmax
  exact
    WilliamsonShmoys.connected_maximal_drawable_graph_edge_count__p2m_7237be62_bb2d_4386_ba18_ecdd0c420d72_a1
      N hcard hN hmax hconn