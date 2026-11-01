-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_of_connected__p2m_f1a10c6f_98ea_4f43_9f3f_2fa486717043_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:22:26.940502+00:00
-- url     : https://prove2.me/submissions/620bc2cd-04e8-4570-8d38-94de7eb431a4

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_d44225cd_db62_4aad_8e63_f30bd1a9ed2e_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_bound__p2m_d44225cd_db62_4aad_8e63_f30bd1a9ed2e_a1 K hK hcard
