-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_induced_edge_bound_large
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:58:43.260203+00:00
-- url     : https://prove2.me/submissions/d66e72bb-50a0-4f45-8bbb-8ee277eeaf64

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_completion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (S : Finset V)
    (hConnected : (H.induce (↑S : Set V)).Connected)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn
      (H.induce (↑S : Set V)))
    (hLarge : 3 ≤ S.card) :
    (H.induce (↑S : Set V)).edgeSet.ncard ≤ 3 * S.card - 6 := by
  let G := H.induce (↑S : Set V)
  have hcard : Fintype.card {x // x ∈ S} = S.card := by
    simp
  obtain ⟨K, _hSubgraph, _hKDrawing, hMono, hTriangulatedCount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulated_completion
      G hConnected hDrawing S.card hLarge hcard
  have hEq : K.edgeSet.ncard = 3 * S.card - 6 := hTriangulatedCount
  calc
    (H.induce (↑S : Set V)).edgeSet.ncard ≤ K.edgeSet.ncard := hMono
    _ = 3 * S.card - 6 := hEq