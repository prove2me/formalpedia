-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_equations_for_edge_bound_584c8b76
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:53:56.937134+00:00
-- url     : https://prove2.me/submissions/f13626d3-b8c0-41a8-af90-90cfa3d96200
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_face_equations_e944d3e8

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet ⊆ M.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = M.edgeSet.ncard + 2 ∧
      3 * f = 2 * M.edgeSet.ncard := by
  have hEdges := WilliamsonShmoys.maximal_planar_edge_count_for_face_equations_e944d3e8
    M hDraw hMax hV
  refine ⟨2 * (Fintype.card V - 2), ?_, ?_⟩ <;> omega