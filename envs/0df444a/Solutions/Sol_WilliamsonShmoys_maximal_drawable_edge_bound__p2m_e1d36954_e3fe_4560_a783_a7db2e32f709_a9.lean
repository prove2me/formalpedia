-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_bound__p2m_e1d36954_e3fe_4560_a783_a7db2e32f709_a9
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T06:54:01.279023+00:00
-- url     : https://prove2.me/submissions/d5c7de7e-c888-4bca-8ffc-4d2b7b83c030

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_edge_count__p2m_3d56d8a6_4977_48bc_b3fc_35028523ea34_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet.ncard ≤ M.edgeSet.ncard) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hDrawN, hEdges⟩ :=
    WilliamsonShmoys.drawable_supergraph_edge_count__p2m_3d56d8a6_4977_48bc_b3fc_35028523ea34_a1
      M hDraw hCard
  calc
    M.edgeSet.ncard ≤ N.edgeSet.ncard :=
      Set.ncard_mono (SimpleGraph.edgeSet_mono hMN)
    _ = 3 * Fintype.card V - 6 := hEdges