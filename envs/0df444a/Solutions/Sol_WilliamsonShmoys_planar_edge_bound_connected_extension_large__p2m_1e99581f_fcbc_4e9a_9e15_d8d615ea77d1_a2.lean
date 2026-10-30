-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_connected_extension_large__p2m_1e99581f_fcbc_4e9a_9e15_d8d615ea77d1_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:31:51.565038+00:00
-- url     : https://prove2.me/submissions/c6c968c2-22d3-4735-8c3c-d2e24e8ae6c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_edge_maximal__p2m_06914e2b_7aee_4867_807c_e684f2b708fd_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_connected__p2m_06914e2b_7aee_4867_807c_e684f2b708fd_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧ K.Connected ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by
  obtain ⟨K, hHK, hKplanar, hCount, hmax⟩ :=
    WilliamsonShmoys.finite_planar_supergraph_edge_maximal__p2m_06914e2b_7aee_4867_807c_e684f2b708fd_a1
      H hplanar
  have hConnected :=
    WilliamsonShmoys.maximal_planar_supergraph_connected__p2m_06914e2b_7aee_4867_807c_e684f2b708fd_a1
      K hKplanar hmax hV
  exact ⟨K, hHK, hKplanar, hConnected, hCount⟩