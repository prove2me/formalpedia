-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_maximal_planar_face_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:50:43.593294+00:00
-- url     : https://prove2.me/submissions/5d5f4d0e-4dbc-4db4-b10c-229f7bdae2b1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_maximal_edge_saturation

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hDraw : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by
  have hUpper := WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound
    L hDraw hCard
  have hLower := WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_maximal_edge_saturation
    L hDraw hMax hCard
  have hEdge : L.edgeSet.ncard + 6 = 3 * Fintype.card V := by omega
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega
