-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_834425e9_b96f_42af_82f3_183711eb71b2_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:10:18.169966+00:00
-- url     : https://prove2.me/submissions/6a373ff4-5463-4372-9081-eb7daa796634

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_d908ff8e_b2ea_4f26_9ee5_97f35f4c9df1_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    L.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  classical
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  obtain ⟨M, hLM, hM, hMax, hLE⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_d908ff8e_b2ea_4f26_9ee5_97f35f4c9df1_a1 L hL
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition M hM hMax hcard
  have hMbound : M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by omega
  exact le_trans hLE hMbound