-- Prove2me | solution 1 for WilliamsonShmoys.planar_maximal_edge_count__p2m_9d0fb3ab_d66a_4954_897e_7905864f2bd9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:59:58.966314+00:00
-- url     : https://prove2.me/submissions/8134b835-9afb-4b3f-9807-827c37726ec3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_b04ea11c_8c6a_4b93_ac52_6786df466eaf_a1
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hPlanar : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  exact WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_b04ea11c_8c6a_4b93_ac52_6786df466eaf_a1 H hPlanar hV