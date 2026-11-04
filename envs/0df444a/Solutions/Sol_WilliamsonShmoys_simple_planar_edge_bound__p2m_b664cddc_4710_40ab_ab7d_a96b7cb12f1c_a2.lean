-- Prove2me | solution 1 for WilliamsonShmoys.simple_planar_edge_bound__p2m_b664cddc_4710_40ab_ab7d_a96b7cb12f1c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:53:26.88723+00:00
-- url     : https://prove2.me/submissions/3d4babeb-3862-4a1e-9cd4-0fd120957492

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_euler_face_count__p2m_61248ae6_40fa_4602_aefc_9bbed6da1387_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hV : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hFaceIncidences⟩ :=
    WilliamsonShmoys.planar_euler_face_count__p2m_61248ae6_40fa_4602_aefc_9bbed6da1387_a1
      K hV hconn hK
  omega