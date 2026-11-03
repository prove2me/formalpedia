-- Prove2me | solution 2 for WilliamsonShmoys.planarEdgeBound_disconnected__p2m_d0c9e92c_0850_4f5e_91b8_72d4ab522367_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:39:53.968199+00:00
-- url     : https://prove2.me/submissions/bee5846f-efda-4e04-bf50-d6a1de74e308

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDisconnectedComponentCounts__p2m_db85b882_89e6_4feb_9146_2311e309823a_a3
import Theorems.Thm_WilliamsonShmoys_componentEdgeSumArithmetic__p2m_db85b882_89e6_4feb_9146_2311e309823a_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hconn : ¬ L.Connected)
    (hn : 3 ≤ Fintype.card V) :
    (letI : DecidableRel L.Adj := dL
     L.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  letI : DecidableRel L.Adj := dL
  obtain ⟨C, edgeCount, hCcard, _hCnonempty, _hCcover, _hCdisjoint,
    hCvertexSum, hEdgeSum, hComponentBound⟩ :=
    WilliamsonShmoys.planarDisconnectedComponentCounts__p2m_db85b882_89e6_4feb_9146_2311e309823a_a3
      L dL hL hconn hn
  exact WilliamsonShmoys.componentEdgeSumArithmetic__p2m_db85b882_89e6_4feb_9146_2311e309823a_a2
    C edgeCount L.edgeFinset.card hCcard hCvertexSum hEdgeSum hComponentBound hn