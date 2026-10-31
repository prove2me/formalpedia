-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_triangulation_augmentation__p2m_dd205c68_bd0c_441d_ba83_4d0ce58e6ad4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:18:15.391545+00:00
-- url     : https://prove2.me/submissions/dc988529-e0a1-4ef2-a6fe-da45e4eefb0b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_0e5c0c9f_81d3_4964_a5b1_5841809db03d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_0e5c0c9f_81d3_4964_a5b1_5841809db03d_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hConnected : K.Connected) (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hKH, hDrawH, hMax⟩ :=
    WilliamsonShmoys.planar_maximal_extension__p2m_0e5c0c9f_81d3_4964_a5b1_5841809db03d_a1
      K hDraw
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_0e5c0c9f_81d3_4964_a5b1_5841809db03d_a1
      H hDrawH hMax hV
  exact ⟨H, hKH, hDrawH, Set.ncard_mono (SimpleGraph.edgeSet_mono hKH), hCount⟩