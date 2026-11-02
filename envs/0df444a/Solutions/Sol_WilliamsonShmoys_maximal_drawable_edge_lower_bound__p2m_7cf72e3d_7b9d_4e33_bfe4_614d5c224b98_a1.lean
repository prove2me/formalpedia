-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_7cf72e3d_7b9d_4e33_bfe4_614d5c224b98_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:11:43.344061+00:00
-- url     : https://prove2.me/submissions/c3ae0b2b-683e-489f-b930-cbd2754c6ab8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_connected__p2m_2752f1ab_5752_4af7_9412_6b19a571a389_a1
import Theorems.Thm_WilliamsonShmoys_connected_maximal_drawable_edge_bound__p2m_2752f1ab_5752_4af7_9412_6b19a571a389_a1
import Mathlib
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M) (hcard : 3 <= Fintype.card V)
    (hmax : forall (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      M <= N -> HasPlanarDrawingOn N -> N = M) :
    3 * Fintype.card V <= M.edgeFinset.card + 6 := by
  have hconn :=
    WilliamsonShmoys.maximal_drawable_connected__p2m_2752f1ab_5752_4af7_9412_6b19a571a389_a1
      M dM hM hcard hmax
  exact
    WilliamsonShmoys.connected_maximal_drawable_edge_bound__p2m_2752f1ab_5752_4af7_9412_6b19a571a389_a1
      M dM hM hcard hmax hconn