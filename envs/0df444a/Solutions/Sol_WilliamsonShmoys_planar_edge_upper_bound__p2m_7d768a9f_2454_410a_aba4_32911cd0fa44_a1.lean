-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_7d768a9f_2454_410a_aba4_32911cd0fa44_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:30:17.715027+00:00
-- url     : https://prove2.me/submissions/e8fbcf5a-bfdb-4a21-b322-3e1cac032d75

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph__p2m_dbd442e1_f792_46a3_a33f_c17e2f3c96c0_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_mono_of_edgeSet_subset__p2m_dbd442e1_f792_46a3_a33f_c17e2f3c96c0_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, hsub, _hK, hcard⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph__p2m_dbd442e1_f792_46a3_a33f_c17e2f3c96c0_a1 H hH hV
  exact le_trans
    (WilliamsonShmoys.edge_count_mono_of_edgeSet_subset__p2m_dbd442e1_f792_46a3_a33f_c17e2f3c96c0_a1 H K hsub)
    (le_of_eq hcard)