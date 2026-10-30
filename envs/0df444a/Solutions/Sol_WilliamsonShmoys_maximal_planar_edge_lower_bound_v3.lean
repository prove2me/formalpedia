-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_v3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T20:02:35.94392+00:00
-- url     : https://prove2.me/submissions/afa0b900-a569-4699-8a60-f3fec18ba641

import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_v1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ H' : SimpleGraph V,
      H ≤ H' → WilliamsonShmoys.HasPlanarDrawingOn H' → H' = H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hKplanar, hK⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_v1 H hH hCard
  have hKH : K = H := hMax K hHK hKplanar
  have hEdges : K.edgeSet.ncard = H.edgeSet.ncard := by rw [hKH]
  omega