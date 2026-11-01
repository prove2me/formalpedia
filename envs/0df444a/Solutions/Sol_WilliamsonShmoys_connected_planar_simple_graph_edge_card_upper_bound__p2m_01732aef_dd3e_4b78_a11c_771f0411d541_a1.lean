-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_simple_graph_edge_card_upper_bound__p2m_01732aef_dd3e_4b78_a11c_771f0411d541_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:17:07.563975+00:00
-- url     : https://prove2.me/submissions/eb26c955-e090-4af2-a6d2-c489f25f8b5b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_simple_graph_euler_face_count__p2m_26b20229_4922_4282_8d13_2bf152659d7b_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_simple_graph_face_incidence_bound__p2m_26b20229_4922_4282_8d13_2bf152659d7b_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      K.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  obtain ⟨f, heuler⟩ := WilliamsonShmoys.connected_planar_simple_graph_euler_face_count__p2m_26b20229_4922_4282_8d13_2bf152659d7b_a1 K hK hconn
  have hface := WilliamsonShmoys.connected_planar_simple_graph_face_incidence_bound__p2m_26b20229_4922_4282_8d13_2bf152659d7b_a1 K hK hconn f heuler
  omega