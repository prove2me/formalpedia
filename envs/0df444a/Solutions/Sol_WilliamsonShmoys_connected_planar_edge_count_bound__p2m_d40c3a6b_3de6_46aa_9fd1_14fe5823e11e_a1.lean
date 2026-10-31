-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_count_bound__p2m_d40c3a6b_3de6_46aa_9fd1_14fe5823e11e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:21:00.378092+00:00
-- url     : https://prove2.me/submissions/85789003-97d4-4256-9758-3df8432b5ce2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_planar_euler_face_inequality__p2m_f59b472f_9ebf_44bd_9cfd_4a86892f90a2_a2
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hHconn : H.Connected)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    planar_euler_face_inequality__p2m_f59b472f_9ebf_44bd_9cfd_4a86892f90a2_a2
      H hV hHconn hHplanar
  omega