-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_vertices_exist__p2m_399eeee6_4234_4eb0_9aa5_260fcba2f92a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:52:46.009648+00:00
-- url     : https://prove2.me/submissions/90cfa607-756c-4dcc-95d7-7edf63f0fdf0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 0 < Fintype.card V)
    (hDisconnected : ¬ ∀ u v, Relation.ReflTransGen G.Adj u v) :
    ∃ u v, ¬ Relation.ReflTransGen G.Adj u v := by
  classical
  push_neg at hDisconnected
  exact hDisconnected