-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_fd5841b3_47d6_4110_a690_9c63bff57c51
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:58:14.913138+00:00
-- url     : https://prove2.me/submissions/d39b07dd-3313-433a-87c8-c47a52cc703f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_connected
import Theorems.Thm_WilliamsonShmoys_connected_maximal_drawable_graph_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      Q ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M ≤ Q) :
    3 * Fintype.card V - 6 = Q.edgeSet.ncard := by
  have hconn : Q.Connected :=
    WilliamsonShmoys.maximal_drawable_graph_connected Q hQ hV hmax
  exact WilliamsonShmoys.connected_maximal_drawable_graph_edge_count
    Q hQ hV hconn hmax