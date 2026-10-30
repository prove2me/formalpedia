-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound_for_maximal_drawing_graph_584c8b76
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:30:10.637729+00:00
-- url     : https://prove2.me/submissions/76638528-9631-4f53-b43f-62095588f2fd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_equations_for_edge_bound_584c8b76

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet ⊆ M.edgeSet) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_face_equations_for_edge_bound_584c8b76
      M hDraw hMax hV
  omega