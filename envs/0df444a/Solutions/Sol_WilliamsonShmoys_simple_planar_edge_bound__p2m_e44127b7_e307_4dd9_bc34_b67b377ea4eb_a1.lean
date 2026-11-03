-- Prove2me | solution 1 for WilliamsonShmoys.simple_planar_edge_bound__p2m_e44127b7_e307_4dd9_bc34_b67b377ea4eb_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:15:55.278195+00:00
-- url     : https://prove2.me/submissions/081b1939-b818-495c-88fb-88d16daf5a11

import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_census__p2m_32bf577a_e5b9_4d87_aee2_e2a1e821aee9_a1
import Theorems.Thm_WilliamsonShmoys_face_census_edge_bound__p2m_32bf577a_e5b9_4d87_aee2_e2a1e821aee9_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    K.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  obtain ⟨F, boundary, hEuler, hDouble, hFaces⟩ :=
    WilliamsonShmoys.planar_drawing_face_census__p2m_32bf577a_e5b9_4d87_aee2_e2a1e821aee9_a1
      K dK hconn hK hcard
  exact WilliamsonShmoys.face_census_edge_bound__p2m_32bf577a_e5b9_4d87_aee2_e2a1e821aee9_a1
    K dK F boundary hEuler hDouble hFaces
