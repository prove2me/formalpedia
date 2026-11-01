-- Prove2me | solution 1 for WilliamsonShmoys.connected_drawing_face_count__p2m_044c324d_acb7_4615_b70a_8b8b8a044876_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:03:50.005109+00:00
-- url     : https://prove2.me/submissions/b1d071b1-54b2-4be0-842a-56879b6ac69a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler__p2m_ae9acfb5_6e8a_4024_8144_fc4b457004a2_a3
import Theorems.Thm_WilliamsonShmoys_simple_planar_drawing_edge_bound__p2m_ae9acfb5_6e8a_4024_8144_fc4b457004a2_a3
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeFinset.card + 2 ∧
      3 * f ≤ 2 * H.edgeFinset.card := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.connected_planar_drawing_euler__p2m_ae9acfb5_6e8a_4024_8144_fc4b457004a2_a3 H hH hconn
  have hEdge :=
    WilliamsonShmoys.simple_planar_drawing_edge_bound__p2m_ae9acfb5_6e8a_4024_8144_fc4b457004a2_a3 H hH hconn hcard
  exact ⟨f, hEuler, by omega⟩