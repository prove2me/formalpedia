-- Prove2me | solution 1 for WilliamsonShmoys_edge_count_mono__p2m_85efdcf1_7002_4c36_9c3f_e040848917fe_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:52:33.292733+00:00
-- url     : https://prove2.me/submissions/d08c6230-b535-4504-b344-c0acf7ddce8e

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  exact Set.ncard_mono (SimpleGraph.edgeSet_mono hGH)