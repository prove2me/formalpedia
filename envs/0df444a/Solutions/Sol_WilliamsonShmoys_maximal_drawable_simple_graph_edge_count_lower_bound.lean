-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_simple_graph_edge_count_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:56:43.22702+00:00
-- url     : https://prove2.me/submissions/581a978b-f0e6-4056-af94-64ad7eb69990
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_augmentation_bound

set_option autoImplicit false

/-- Maximality identifies the graph with an edge-rich planar augmentation. -/
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hMax : ∀ U : SimpleGraph V,
      G ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = G) :
    3 * Fintype.card V - 6 ≤ G.edgeSet.ncard := by
  obtain ⟨U, hGU, hU, hEdges⟩ :=
    WilliamsonShmoys.planar_drawing_edge_augmentation_bound G hV hG
  have hEq : U = G := hMax U hGU hU
  rw [hEq] at hEdges
  exact hEdges