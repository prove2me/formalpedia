-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_of_arcs
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:02:59.498819+00:00
-- url     : https://prove2.me/submissions/a7493448-ad15-4d96-84db-f801fa9fd2b7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_for_arcs
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hNDrawing, hNCount⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_count_for_arcs M hDrawing hCard
  have hNM : N = M := hMax N hMN hNDrawing
  simpa [hNM] using hNCount