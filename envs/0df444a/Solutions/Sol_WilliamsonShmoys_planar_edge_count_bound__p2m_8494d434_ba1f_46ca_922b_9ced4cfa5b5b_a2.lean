-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_bound__p2m_8494d434_ba1f_46ca_922b_9ced4cfa5b5b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T01:03:26.755482+00:00
-- url     : https://prove2.me/submissions/61fbacdb-f83b-47ee-a61d-b73b85716d38

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_face_census__p2m_e0605b2b_a2c2_4550_811f_f61ce2015061_a1
import Theorems.Thm_WilliamsonShmoys_edge_bound_from_face_census__p2m_e0605b2b_a2c2_4550_811f_f61ce2015061_a1
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨f, heuler, hface⟩ :=
    WilliamsonShmoys.planar_face_census__p2m_e0605b2b_a2c2_4550_811f_f61ce2015061_a1
      H hplanar hconnected hV
  exact WilliamsonShmoys.edge_bound_from_face_census__p2m_e0605b2b_a2c2_4550_811f_f61ce2015061_a1
    (Fintype.card V) H.edgeSet.ncard f heuler hface