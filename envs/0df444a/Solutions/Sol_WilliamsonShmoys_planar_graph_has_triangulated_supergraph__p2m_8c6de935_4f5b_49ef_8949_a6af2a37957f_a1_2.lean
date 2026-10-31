-- Prove2me | solution 2 for WilliamsonShmoys.planar_graph_has_triangulated_supergraph__p2m_8c6de935_4f5b_49ef_8949_a6af2a37957f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:40:57.2836+00:00
-- url     : https://prove2.me/submissions/5b5b3275-b32f-4e47-8173-69baf663be5e

import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      G ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_supergraph_triangulation G hG hV
