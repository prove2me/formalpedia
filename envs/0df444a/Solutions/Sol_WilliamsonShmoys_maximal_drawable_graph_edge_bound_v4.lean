-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_bound_v4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:29:45.341304+00:00
-- url     : https://prove2.me/submissions/1d952b8f-6df1-46e2-9b77-d50f30fe17ab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_bound_v4_triangulated_supergraph

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    3 * (Fintype.card V : Int) - 6 ≤ (M.edgeSet.ncard : Int) := by
  obtain ⟨N, hMN, hNdraw, hNcard⟩ :=
    WilliamsonShmoys.maximal_drawable_graph_edge_bound_v4_triangulated_supergraph
      M hdraw hV
  have hNM : N ≤ M := hmax N hMN hNdraw
  have hEq : N = M := le_antisymm hNM hMN
  rw [hEq] at hNcard
  exact le_of_eq hNcard.symm