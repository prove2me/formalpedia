-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_5db12fa6_6ddb_45ce_9ff4_a1f528d0a813_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:56:23.594441+00:00
-- url     : https://prove2.me/submissions/96865c38-0249-46c2-8388-eb238a1969c1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_face_count_of_drawing__p2m_7f93d6a5_e061_4fd9_b77a_4e628bac87b4_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨f, hEuler, hFace⟩ :=
    WilliamsonShmoys.planar_simple_graph_face_count_of_drawing__p2m_7f93d6a5_e061_4fd9_b77a_4e628bac87b4_a1
      H hH hconn hV
  omega