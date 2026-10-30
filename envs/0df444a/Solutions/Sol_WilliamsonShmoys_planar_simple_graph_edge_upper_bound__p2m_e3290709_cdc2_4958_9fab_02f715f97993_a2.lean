-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_e3290709_cdc2_4958_9fab_02f715f97993_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:00:23.547538+00:00
-- url     : https://prove2.me/submissions/10e3ffc7-d6c9-4f4f-b607-28da7f1d9e30
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_03ccc876_b6bf_43b7_928a_d41b56ffed25_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_upper_bound__p2m_03ccc876_b6bf_43b7_928a_d41b56ffed25_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, instK, hSub, hKConnected, hKPlanar⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_03ccc876_b6bf_43b7_928a_d41b56ffed25_a1
      H hH hcard
  letI : DecidableRel K.Adj := instK
  exact (Finset.card_le_card hSub).trans
    (WilliamsonShmoys.connected_planar_edge_upper_bound__p2m_03ccc876_b6bf_43b7_928a_d41b56ffed25_a1
      K hKPlanar hKConnected hcard)