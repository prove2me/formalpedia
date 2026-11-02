-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_euler_face_count__p2m_688f1835_390c_48d2_a756_3ce127433083_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:43:44.187222+00:00
-- url     : https://prove2.me/submissions/71a7b58b-9682-4060-9044-251fea938be8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound_from_drawing__p2m_2ca2cc35_45b9_454e_9480_d6c447ab0740_a1
import Theorems.Thm_WilliamsonShmoys_connected_edge_count_lower_bound__p2m_2ca2cc35_45b9_454e_9480_d6c447ab0740_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     ∃ f : ℕ,
       Fintype.card V + f = H.edgeFinset.card + 2 ∧
       3 * f ≤ 2 * H.edgeFinset.card) := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hedge := WilliamsonShmoys.simple_planar_edge_bound_from_drawing__p2m_2ca2cc35_45b9_454e_9480_d6c447ab0740_a1
    H hcard hconn hH
  have hconnE := WilliamsonShmoys.connected_edge_count_lower_bound__p2m_2ca2cc35_45b9_454e_9480_d6c447ab0740_a1
    H hconn
  refine ⟨H.edgeFinset.card + 2 - Fintype.card V, ?_, ?_⟩ <;> omega