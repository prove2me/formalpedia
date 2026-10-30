-- Prove2me | solution 1 for WilliamsonShmoys.finite_planar_supergraph_edge_maximal__p2m_06914e2b_7aee_4867_807c_e684f2b708fd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:55:47.326879+00:00
-- url     : https://prove2.me/submissions/703e7894-58f9-4edc-865c-d24db3700dd5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_maximal_extension__p2m_dfeab8e7_c65a_497d_a20d_7cce49bd8d27_a2

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hplanar : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L →
        L.edgeSet.ncard ≤ K.edgeSet.ncard := by
  exact WilliamsonShmoys.finite_graph_maximal_extension__p2m_dfeab8e7_c65a_497d_a20d_7cce49bd8d27_a2
    (P := HasPlanarDrawingOn) H hplanar
