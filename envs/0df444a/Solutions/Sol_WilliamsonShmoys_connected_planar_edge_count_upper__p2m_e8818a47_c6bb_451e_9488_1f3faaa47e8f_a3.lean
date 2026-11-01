-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_count_upper__p2m_e8818a47_c6bb_451e_9488_1f3faaa47e8f_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:14:11.848496+00:00
-- url     : https://prove2.me/submissions/3e1779a1-5365-4cc9-bfc9-baa789af8e0f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_face_certificate__p2m_42c50023_969e_4d67_9641_cde1dc4669ab_a2
import Theorems.Thm_WilliamsonShmoys_planar_face_certificate_edge_bound__p2m_42c50023_969e_4d67_9641_cde1dc4669ab_a2
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      K.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  classical
  obtain ⟨faceCount, hboundary, heuler⟩ :=
    WilliamsonShmoys.connected_planar_face_certificate__p2m_42c50023_969e_4d67_9641_cde1dc4669ab_a2
      K hK hconn hcard
  exact WilliamsonShmoys.planar_face_certificate_edge_bound__p2m_42c50023_969e_4d67_9641_cde1dc4669ab_a2
    K faceCount hcard hboundary heuler