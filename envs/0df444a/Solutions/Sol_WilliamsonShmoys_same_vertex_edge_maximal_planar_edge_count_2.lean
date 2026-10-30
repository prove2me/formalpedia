-- Prove2me | solution 2 for WilliamsonShmoys.same_vertex_edge_maximal_planar_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:55:06.397224+00:00
-- url     : https://prove2.me/submissions/09b7ad51-c294-432c-a71a-4ce858af4c3c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_completion

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  first
  | exact _root_.WilliamsonShmoys.edge_count_of_maximal_planar_completion
  | (apply _root_.WilliamsonShmoys.edge_count_of_maximal_planar_completion <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.edge_count_of_maximal_planar_completion <;> assumption)
