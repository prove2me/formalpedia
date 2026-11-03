-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_count__p2m_0951cfca_b350_4b14_85c9_9d9dc14f4b38_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:46:01.749401+00:00
-- url     : https://prove2.me/submissions/0bff7267-f5aa-4c0b-9efb-c9f1dde103c6

import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_bound__p2m_f80212f3_e77c_4cfe_8939_73f581dec5be_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hconn : ∀ u v : V, Nonempty (J.Walk u v))
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    J.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
    fun K => Classical.decRel K.Adj
  obtain ⟨f, heuler, hfaces⟩ :=
    WilliamsonShmoys.connected_planar_drawing_euler_face_bound__p2m_f80212f3_e77c_4cfe_8939_73f581dec5be_a1
      J hJ hconn hcard
  omega
