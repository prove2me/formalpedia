-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_count_bound__p2m_2c123b8f_1995_4892_9bf1_663a03a79ac0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:43:53.349446+00:00
-- url     : https://prove2.me/submissions/02293887-2427-4bdc-ad7f-57985adfc5b1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_4f0f4017_69c8_49f6_a405_0b1a215ecea7_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_of_edge_maximal_planar_graph__p2m_4f0f4017_69c8_49f6_a405_0b1a215ecea7_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hconn : L.Connected) (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      L.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  classical
  obtain ⟨H, hLH, hconnH, hplanarH, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_4f0f4017_69c8_49f6_a405_0b1a215ecea7_a1
      L hL hconn
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hcount :=
    WilliamsonShmoys.edge_count_of_edge_maximal_planar_graph__p2m_4f0f4017_69c8_49f6_a405_0b1a215ecea7_a1
      H hplanarH hconnH hcard hmax
  have hle : L.edgeFinset.card ≤ H.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hLH)
  omega