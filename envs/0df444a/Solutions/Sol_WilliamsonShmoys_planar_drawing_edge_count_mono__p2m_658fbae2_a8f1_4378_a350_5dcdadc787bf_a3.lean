-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_mono__p2m_658fbae2_a8f1_4378_a350_5dcdadc787bf_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:19:22.93099+00:00
-- url     : https://prove2.me/submissions/3c1edfb2-4647-4866-84d8-d06771b61334

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (G M : SimpleGraph V)
    (hGM : G ≤ M) :
    G.edgeSet.ncard ≤ M.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGM)