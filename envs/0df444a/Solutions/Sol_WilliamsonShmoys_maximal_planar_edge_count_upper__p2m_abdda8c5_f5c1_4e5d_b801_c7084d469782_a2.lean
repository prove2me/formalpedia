-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_abdda8c5_f5c1_4e5d_b801_c7084d469782_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T20:50:31.937153+00:00
-- url     : https://prove2.me/submissions/8dc4f600-2ad8-4e3a-9542-d751e46ebffa

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_bound__p2m_a37fca92_b240_4415_b2f0_be56bbb8e59b_a1
import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph__p2m_a37fca92_b240_4415_b2f0_be56bbb8e59b_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hsub, hKconn, hKplanar⟩ :=
    WilliamsonShmoys.planar_connected_supergraph__p2m_a37fca92_b240_4415_b2f0_be56bbb8e59b_a1
      H hH hV
  have hbound :=
    WilliamsonShmoys.planar_connected_edge_bound__p2m_a37fca92_b240_4415_b2f0_be56bbb8e59b_a1
      K hKplanar hKconn hV
  have hcard : H.edgeSet.ncard ≤ K.edgeSet.ncard := Set.ncard_mono hsub
  omega