-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_edge_rank_bound__p2m_9fc762a8_5f43_4315_941e_21ea4c59e3e4_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:33:44.394737+00:00
-- url     : https://prove2.me/submissions/55dddc50-d355-4ae4-9d11-d31833c57579

import Theorems.Thm_WilliamsonShmoys_edge_ncard_bounded__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a3

import Mathlib

theorem solution
    {V : Type} [Fintype V] (G : SimpleGraph V) :
    G.edgeSet.ncard ≤ Fintype.card (Sym2 V) :=
  WilliamsonShmoys.edge_ncard_bounded__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a3 G