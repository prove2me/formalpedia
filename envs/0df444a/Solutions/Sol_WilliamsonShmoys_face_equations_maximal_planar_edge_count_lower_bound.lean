-- Prove2me | solution 1 for WilliamsonShmoys.face_equations_maximal_planar_edge_count_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:46:12.222775+00:00
-- url     : https://prove2.me/submissions/5ca5cb5c-bb87-4bbe-b740-ab94125d27b3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_face_equations_triangulation_completion

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
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  obtain ⟨N, hMN, hNDraw, hCount⟩ :=
    WilliamsonShmoys.face_equations_triangulation_completion M hDraw hV
  have hNM := hMax N hMN hNDraw
  have hEdges : M.edgeSet = N.edgeSet := Set.Subset.antisymm hMN hNM
  simpa [hEdges] using hCount.symm.le