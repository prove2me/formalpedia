-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_count_from_connected__p2m_8a1edb89_91b7_4c19_a333_1779b45ebb8a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T10:03:58.816969+00:00
-- url     : https://prove2.me/submissions/81d738c3-295a-4408-9192-89a2b93a20f7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_0d663055_40d3_4575_b5af_11ff2bc59459_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hconnBound : ∀ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      H.Connected → HasPlanarDrawingOn H → 3 ≤ Fintype.card V →
      (letI : DecidableRel H.Adj := dH
       H.edgeFinset.card ≤ 3 * Fintype.card V - 6))
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG
     G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  letI : DecidableRel G.Adj := dG
  exact WilliamsonShmoys.planar_edge_count_upper_bound__p2m_0d663055_40d3_4575_b5af_11ff2bc59459_a1 G hG hcard