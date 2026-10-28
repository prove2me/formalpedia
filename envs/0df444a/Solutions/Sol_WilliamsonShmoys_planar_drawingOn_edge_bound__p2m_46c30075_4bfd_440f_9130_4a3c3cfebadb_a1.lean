-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_edge_bound__p2m_46c30075_4bfd_440f_9130_4a3c3cfebadb_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:24:47.43499+00:00
-- url     : https://prove2.me/submissions/bfb535a8-3a8c-479c-958b-b4af6edef572
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_extension__p2m_6ea4c7f0_554c_4055_b163_042ee1bb88bc_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count__p2m_6ea4c7f0_554c_4055_b163_042ee1bb88bc_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hSub, hDrawing, hMax⟩ :=
    WilliamsonShmoys.planar_drawingOn_maximal_extension__p2m_6ea4c7f0_554c_4055_b163_042ee1bb88bc_a1
      G hG
  have hCount :=
    WilliamsonShmoys.maximal_planar_drawingOn_edge_count__p2m_6ea4c7f0_554c_4055_b163_042ee1bb88bc_a1
      H hDrawing hMax hCard
  have hEdges : G.edgeSet.ncard ≤ H.edgeSet.ncard := Set.ncard_mono hSub
  omega