-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_edge_count__p2m_397071d2_54cd_4807_97e7_b4001b0535bd_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:44:41.863787+00:00
-- url     : https://prove2.me/submissions/a580e9d3-c32f-4c02-880d-4c73829071f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_77de69cb_c537_4581_bdbd_5f8e6aadfa5a_a1
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count_lower_bound__p2m_77de69cb_c537_4581_bdbd_5f8e6aadfa5a_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M -> HasPlanarDrawingOn M -> M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper :
      L.edgeSet.ncard <= 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_edge_count_upper_bound__p2m_77de69cb_c537_4581_bdbd_5f8e6aadfa5a_a1
      L hV hL
  have hLower :
      3 * Fintype.card V - 6 <= L.edgeSet.ncard :=
    WilliamsonShmoys.edge_maximal_planar_edge_count_lower_bound__p2m_77de69cb_c537_4581_bdbd_5f8e6aadfa5a_a1
      L hV hL hmax
  omega