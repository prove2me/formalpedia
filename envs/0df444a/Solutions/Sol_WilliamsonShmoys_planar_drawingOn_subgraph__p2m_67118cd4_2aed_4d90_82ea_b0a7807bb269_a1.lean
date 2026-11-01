-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_subgraph__p2m_67118cd4_2aed_4d90_82ea_b0a7807bb269_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:19:31.908142+00:00
-- url     : https://prove2.me/submissions/b9383337-a3e6-456b-807c-2aa4110e1cbf

import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_subgraph__p2m_cf7c4288_a938_4a87_b27f_3fd599c4349b_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hHG : H.edgeSet ⊆ G.edgeSet)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    WilliamsonShmoys.HasPlanarDrawingOn H :=
  WilliamsonShmoys.planarDrawingOn_subgraph__p2m_cf7c4288_a938_4a87_b27f_3fd599c4349b_a1 hHG hG
