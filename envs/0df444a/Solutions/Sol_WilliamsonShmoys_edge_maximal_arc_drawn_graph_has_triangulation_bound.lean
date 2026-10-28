-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_arc_drawn_graph_has_triangulation_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:44:30.333706+00:00
-- url     : https://prove2.me/submissions/79cb32c5-baab-48ef-ac91-33780de64a02
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_edge_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  obtain ⟨N, hMN, hN, hbound⟩ :=
    WilliamsonShmoys.planar_drawing_completion_edge_bound M hV hM
  have hNM : N ≤ M := hmax N hMN hN
  have hEq : N = M := le_antisymm hNM hMN
  rw [← hEq]
  exact hbound