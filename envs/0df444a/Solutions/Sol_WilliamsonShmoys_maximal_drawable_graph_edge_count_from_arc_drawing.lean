-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_from_arc_drawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:29:04.284269+00:00
-- url     : https://prove2.me/submissions/2ae20c8b-1b43-402e-9aed-e2a70af68df9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_drawable_completion_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨H, hNH, hH, hcard⟩ :=
    WilliamsonShmoys.exists_drawable_completion_edge_count N hV hN
  have hHN : H ≤ N := hmax H hNH hH
  have heq : N = H := le_antisymm hNH hHN
  rw [heq]
  exact hcard