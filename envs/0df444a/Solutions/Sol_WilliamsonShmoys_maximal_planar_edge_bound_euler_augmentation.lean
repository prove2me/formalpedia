-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound_euler_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:40:28.627993+00:00
-- url     : https://prove2.me/submissions/25efad01-0b20-4331-975a-c106916f7954

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_edge_count_maximal

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V,
      G.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet = G.edgeSet) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by
  obtain ⟨L, hSub, hDrawL, hCount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_edge_count_maximal G hDraw hCard
  have hEdge : L.edgeSet = G.edgeSet := hMax L hSub hDrawL
  simpa [hEdge] using hCount.le
