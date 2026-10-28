-- Prove2me | solution 1 for WilliamsonShmoys.drawable_supergraph_edge_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:10:05.909205+00:00
-- url     : https://prove2.me/submissions/21554a68-02c5-4176-9944-98d539ca26ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_maximal_exists_v2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_bound_v2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn T) (hV : 3 ≤ Fintype.card V) :
    ∃ U : SimpleGraph V, T ≤ U ∧ HasPlanarDrawingOn U ∧
      3 * Fintype.card V ≤ U.edgeSet.ncard + 6 := by
  obtain ⟨U, hTU, hUdraw, hUmax⟩ :=
    WilliamsonShmoys.drawable_supergraph_maximal_exists_v2 T hdraw
  exact ⟨U, hTU, hUdraw,
    WilliamsonShmoys.maximal_drawable_edge_bound_v2 U hUdraw hUmax hV⟩