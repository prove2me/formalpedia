-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_680be9fd_c5aa_487c_a8fd_ae4516866871_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:18:29.400535+00:00
-- url     : https://prove2.me/submissions/8c7c790c-0db1-4854-b6a8-77facc826308

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_count_certificate__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a2__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a3
import Theorems.Thm_WilliamsonShmoys_planar_face_count_edge_bound__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a2__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a3

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V)
    (hmax : forall H : SimpleGraph V, K <= H -> WilliamsonShmoys.HasPlanarDrawingOn H -> H <= K) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  exact WilliamsonShmoys.planar_face_count_edge_bound__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a2__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a3 K
    (WilliamsonShmoys.maximal_planar_drawing_face_count_certificate__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a2__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a3 K hK hV hmax)