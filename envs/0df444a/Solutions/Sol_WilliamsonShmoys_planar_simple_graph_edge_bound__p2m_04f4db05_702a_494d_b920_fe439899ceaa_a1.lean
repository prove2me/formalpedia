-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_04f4db05_702a_494d_b920_fe439899ceaa_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T22:40:50.892272+00:00
-- url     : https://prove2.me/submissions/ed82dbe0-7f44-45d2-bfdb-597990241b67

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count__p2m_20aae0e7_47ce_430e_848b_f31970e65b06_a5

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨F, hEuler, hfaces⟩ :=
    WilliamsonShmoys.planar_drawing_face_count__p2m_20aae0e7_47ce_430e_848b_f31970e65b06_a5
      K hconn hdraw hV
  omega