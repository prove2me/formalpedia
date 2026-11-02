-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_2e383da1_b0fd_42ac_bf20_409641577930_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:50:31.956203+00:00
-- url     : https://prove2.me/submissions/8f2875f1-5adb-4e88-9d46-e91d020faf06
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_1450b57d_ff3f_4f0e_9779_6941f1e67e4b_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_1450b57d_ff3f_4f0e_9779_6941f1e67e4b_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
  obtain ⟨H, hKH, hconnected, hHdraw, hcard_edges⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension__p2m_1450b57d_ff3f_4f0e_9779_6941f1e67e4b_a1
      K hcard hdraw
  exact hcard_edges.trans
    (WilliamsonShmoys.connected_planar_edge_bound__p2m_1450b57d_ff3f_4f0e_9779_6941f1e67e4b_a1
      H hcard hconnected hHdraw)
