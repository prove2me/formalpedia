-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulated_supergraph__p2m_7a004575_a295_4f3c_8d74_3fb00efa8d41_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:23:05.336654+00:00
-- url     : https://prove2.me/submissions/1dd7e5d7-bd1f-4f82-92a0-55549aa6362b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_ef9c63a2_b89d_412e_ad8e_f938ea808c23_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_ef9c63a2_b89d_412e_ad8e_f938ea808c23_a2
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph__p2m_ef9c63a2_b89d_412e_ad8e_f938ea808c23_a2 H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_ef9c63a2_b89d_412e_ad8e_f938ea808c23_a2
      K hK hV hmax⟩