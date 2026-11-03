-- Prove2me | solution 1 for WilliamsonShmoys.simple_planar_edge_bound_from_drawing__p2m_2ca2cc35_45b9_454e_9480_d6c447ab0740_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:05:36.439207+00:00
-- url     : https://prove2.me/submissions/fba05965-5d86-48eb-b3c1-6968b56caeca

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_bound_data__p2m_cd539f9d_43c0_4104_8907_5b455d63330b_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.planar_drawing_euler_bound_data__p2m_cd539f9d_43c0_4104_8907_5b455d63330b_a2
      H hcard hconn hH
  omega