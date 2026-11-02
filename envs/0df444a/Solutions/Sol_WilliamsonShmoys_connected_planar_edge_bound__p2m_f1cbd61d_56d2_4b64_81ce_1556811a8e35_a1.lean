-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_f1cbd61d_56d2_4b64_81ce_1556811a8e35_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:13:44.918933+00:00
-- url     : https://prove2.me/submissions/aca32da6-c58c-4b57-842a-08684aba27d6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_face_count_from_drawing__p2m_c508f2ea_079b_4849_b4cc_0b3b748b75aa_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_face_count__p2m_c508f2ea_079b_4849_b4cc_0b3b748b75aa_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hn : Nat.le 3 (Fintype.card V)) :
    Nat.le H.edgeFinset.card (3 * Fintype.card V - 6) := by
  obtain ⟨f, heuler, hdegree⟩ :=
    WilliamsonShmoys.planar_face_count_from_drawing__p2m_c508f2ea_079b_4849_b4cc_0b3b748b75aa_a1
      H dH hconn hH hn
  exact WilliamsonShmoys.planar_edge_bound_from_face_count__p2m_c508f2ea_079b_4849_b4cc_0b3b748b75aa_a1
    (Fintype.card V) H.edgeFinset.card f hn heuler hdegree