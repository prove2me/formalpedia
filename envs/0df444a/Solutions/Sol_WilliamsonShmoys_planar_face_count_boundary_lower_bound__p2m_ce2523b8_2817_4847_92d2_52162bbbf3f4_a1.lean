-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_count_boundary_lower_bound__p2m_ce2523b8_2817_4847_92d2_52162bbbf3f4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:13:17.582277+00:00
-- url     : https://prove2.me/submissions/1d28f47e-3c89-4d7b-9f43-6be2996fdff1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_3a4c1f5e_1776_4c15_8093_87a5faec746f_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected) (hcard : 3 ≤ Fintype.card V)
    (f : ℕ)
    (hEuler : Fintype.card V + f = M.edgeFinset.card + 2) :
    3 * f ≤ 2 * M.edgeFinset.card := by
  have hedge := WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_3a4c1f5e_1776_4c15_8093_87a5faec746f_a1
    M hM hconn hcard
  omega