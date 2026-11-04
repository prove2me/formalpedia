-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_face_certificate__p2m_42c50023_969e_4d67_9641_cde1dc4669ab_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:20:46.420057+00:00
-- url     : https://prove2.me/submissions/b4f624cc-913f-48a6-9af6-531588e75228

import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_87b40329_c584_43e3_b2a8_a209b09780ca_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_boundary_lengths_at_euler_count__p2m_87b40329_c584_43e3_b2a8_a209b09780ca_a2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ faceCount : Nat,
      (∃ boundaryLength : Fin faceCount → Nat,
        (∑ f : Fin faceCount, boundaryLength f) = 2 * K.edgeFinset.card ∧
        (∀ f : Fin faceCount, 3 ≤ boundaryLength f)) ∧
      Fintype.card V + faceCount = K.edgeFinset.card + 2 := by
  obtain ⟨faceCount, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_count__p2m_87b40329_c584_43e3_b2a8_a209b09780ca_a2
      K hK hconn hcard
  refine ⟨faceCount, ?_, hEuler⟩
  exact WilliamsonShmoys.planar_drawing_boundary_lengths_at_euler_count__p2m_87b40329_c584_43e3_b2a8_a209b09780ca_a2
    K hK hconn hcard faceCount hEuler
