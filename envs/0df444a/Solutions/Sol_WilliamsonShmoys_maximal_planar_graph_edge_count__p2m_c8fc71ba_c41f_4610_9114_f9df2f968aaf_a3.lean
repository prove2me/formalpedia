-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_c8fc71ba_c41f_4610_9114_f9df2f968aaf_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:01:33.051716+00:00
-- url     : https://prove2.me/submissions/6c61ca44-1a5a-4d44-8af3-5ee105cfe0f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_0f5981a3_7974_4822_a476_e1c2ba671214_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_0f5981a3_7974_4822_a476_e1c2ba671214_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hP : HasPlanarDrawingOn P)
    (hmax : ∀ Q : SimpleGraph V,
      (∀ u v, P.Adj u v → Q.Adj u v) →
      HasPlanarDrawingOn Q →
      (∀ u v, Q.Adj u v → P.Adj u v)) :
    3 * Fintype.card V = P.edgeSet.ncard + 6 := by
  have hupper := WilliamsonShmoys.planar_edge_upper_bound__p2m_0f5981a3_7974_4822_a476_e1c2ba671214_a1
    P hcard hP
  have hlower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_0f5981a3_7974_4822_a476_e1c2ba671214_a1
    P hcard hP hmax
  omega
