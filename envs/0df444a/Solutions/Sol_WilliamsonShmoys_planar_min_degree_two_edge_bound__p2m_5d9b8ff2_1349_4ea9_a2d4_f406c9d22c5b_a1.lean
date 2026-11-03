-- Prove2me | solution 1 for WilliamsonShmoys.planar_min_degree_two_edge_bound__p2m_5d9b8ff2_1349_4ea9_a2d4_f406c9d22c5b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:54:19.121992+00:00
-- url     : https://prove2.me/submissions/573de8cd-8960-4e89-98f3-8fc918848c67

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_d44225cd_db62_4aad_8e63_f30bd1a9ed2e_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 <= Fintype.card V)
    (hdegree : ∀ v : V, 2 <= (K.neighborSet v).ncard) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_bound__p2m_d44225cd_db62_4aad_8e63_f30bd1a9ed2e_a1 K hK hcard