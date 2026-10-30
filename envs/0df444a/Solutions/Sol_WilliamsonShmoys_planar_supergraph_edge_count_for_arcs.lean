-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_count_for_arcs
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:15:17.714201+00:00
-- url     : https://prove2.me/submissions/253828a1-6264-4cfd-9b01-20649dbe65b9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_on_for_arcs
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_arcs

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨N, hMN, hNDrawing, hMaximal⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_on_for_arcs M hDrawing
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count_for_arcs N hNDrawing hCard hMaximal
  exact ⟨N, hMN, hNDrawing, hCount⟩