-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:48:25.774812+00:00
-- url     : https://prove2.me/submissions/15fe6557-fc18-4cff-bf63-6bdae258fa28

import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_supergraph_edge_count_bound

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHcard⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulated_supergraph_edge_count_bound G hG hCard
  have hle : G.edgeSet.ncard <= H.edgeSet.ncard := Set.ncard_mono hGH
  omega