-- Prove2me | solution 1 for WilliamsonShmoys.spanning_triangulation__p2m_cc516969_790b_410d_8fc5_8fd17bba7f5b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:23:41.722198+00:00
-- url     : https://prove2.me/submissions/ed583a33-4b35-4b9a-9148-1ff649315931
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_24fa2186_c188_443b_b73b_9b81dd69fcd0_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_24fa2186_c188_443b_b73b_9b81dd69fcd0_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {U : Type} [Fintype U] [LinearOrder U]
    (G : SimpleGraph U) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) (hcard : 3 ≤ Fintype.card U) :
    ∃ H : SimpleGraph U, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card U := by
  obtain ⟨H, hGH, hHdraw, hHmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph__p2m_24fa2186_c188_443b_b73b_9b81dd69fcd0_a1
      G hdraw hconn hcard
  exact ⟨H, hGH, hHdraw,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_24fa2186_c188_443b_b73b_9b81dd69fcd0_a1
      H hHdraw hHmax hcard⟩