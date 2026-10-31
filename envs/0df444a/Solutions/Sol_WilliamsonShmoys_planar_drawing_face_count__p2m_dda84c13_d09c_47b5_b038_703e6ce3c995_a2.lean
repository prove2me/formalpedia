-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_count__p2m_dda84c13_d09c_47b5_b038_703e6ce3c995_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:28:52.938118+00:00
-- url     : https://prove2.me/submissions/bc7c086a-3874-441f-9838-19db23c49c5c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_euler_face_count__p2m_d44225cd_db62_4aad_8e63_f30bd1a9ed2e_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_d44225cd_db62_4aad_8e63_f30bd1a9ed2e_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 <= Fintype.card V) :
    Exists fun f : Nat =>
      Fintype.card V + f = K.edgeSet.ncard + 2 /\
      3 * f <= 2 * K.edgeSet.ncard := by
  obtain ⟨f, heuler⟩ := WilliamsonShmoys.planar_euler_face_count__p2m_d44225cd_db62_4aad_8e63_f30bd1a9ed2e_a1 K hK hconn
  have hedge := WilliamsonShmoys.planar_edge_bound__p2m_d44225cd_db62_4aad_8e63_f30bd1a9ed2e_a1 K hK hV
  exact ⟨f, heuler, by omega⟩