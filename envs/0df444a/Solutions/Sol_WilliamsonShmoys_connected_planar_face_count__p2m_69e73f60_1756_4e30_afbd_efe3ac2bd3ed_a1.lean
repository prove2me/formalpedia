-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_face_count__p2m_69e73f60_1756_4e30_afbd_efe3ac2bd3ed_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:40:21.970388+00:00
-- url     : https://prove2.me/submissions/02279487-4301-462d-be06-aeaba96d1e28
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_face_count__p2m_7e43e1d3_8cc5_4078_adc3_512d6b4c19e6_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_7e43e1d3_8cc5_4078_adc3_512d6b4c19e6_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hconn : N.Connected) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     ∃ f : ℕ,
       Fintype.card V + f = N.edgeFinset.card + 2 ∧
       3 * f ≤ 2 * N.edgeFinset.card) := by
  classical
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.connected_planar_euler_face_count__p2m_7e43e1d3_8cc5_4078_adc3_512d6b4c19e6_a1
      N hcard hN hconn
  have hEdge :=
    WilliamsonShmoys.connected_planar_edge_bound__p2m_7e43e1d3_8cc5_4078_adc3_512d6b4c19e6_a1
      N hcard hN hconn
  exact ⟨f, hEuler, by omega⟩