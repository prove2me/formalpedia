-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_76a86dc1_411a_4f86_8755_ab6ac02ce22d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:11:36.55859+00:00
-- url     : https://prove2.me/submissions/9d4d5530-8df2-43da-96e4-9fed1d596b05
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_upper_bound__p2m_bfc81ce3_c50f_433a_ae04_d243cae0dc3b_a1
import Theorems.Thm_WilliamsonShmoys_planar_graph_connected_supergraph__p2m_bfc81ce3_c50f_433a_ae04_d243cae0dc3b_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    T.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨U, hTU, hUConnected, hUPlanar⟩ :=
    WilliamsonShmoys.planar_graph_connected_supergraph__p2m_bfc81ce3_c50f_433a_ae04_d243cae0dc3b_a1
      T hT
  calc
    T.edgeSet.ncard ≤ U.edgeSet.ncard :=
      Set.ncard_mono (SimpleGraph.edgeSet_mono hTU)
    _ ≤ 3 * Fintype.card V - 6 :=
      WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_bfc81ce3_c50f_433a_ae04_d243cae0dc3b_a1
        U hV hUPlanar hUConnected