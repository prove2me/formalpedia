-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_444cd434_7013_46bb_9e82_d756827f6b0e_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T20:47:11.2522+00:00
-- url     : https://prove2.me/submissions/e8205e1c-2dfe-4058-b471-efd2333a86ac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound_connected__p2m_a2ea7bef_e32d_429b_9bbe_071fb272fdb7_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_a2ea7bef_e32d_429b_9bbe_071fb272fdb7_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    K.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  classical
  obtain ⟨H, hKH, hconn, hplanar⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_a2ea7bef_e32d_429b_9bbe_071fb272fdb7_a1
      K dK hK
  let dH : DecidableRel H.Adj := Classical.decRel _
  have hbound :=
    WilliamsonShmoys.planar_simple_graph_edge_upper_bound_connected__p2m_a2ea7bef_e32d_429b_9bbe_071fb272fdb7_a1
      H dH hconn hplanar hcard
  exact (Finset.card_le_card (SimpleGraph.edgeFinset_mono hKH)).trans hbound