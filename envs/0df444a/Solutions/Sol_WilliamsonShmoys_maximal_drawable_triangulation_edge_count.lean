-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_triangulation_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T23:21:16.038703+00:00
-- url     : https://prove2.me/submissions/b80c52b9-ca54-4410-8b14-da683ae83a37
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_simple_graph_edge_bound
import Theorems.Thm_WilliamsonShmoys_drawable_graph_edge_augmentation

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hmax : ∀ Y : SimpleGraph V, X ≤ Y → WilliamsonShmoys.HasPlanarDrawingOn Y → Y = X)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = X.edgeSet.ncard + 6 := by
  have hupper := WilliamsonShmoys.drawable_simple_graph_edge_bound X hdraw hV
  have hlower : 3 * Fintype.card V ≤ X.edgeSet.ncard + 6 := by
    by_contra h
    have hsmall : X.edgeSet.ncard + 6 < 3 * Fintype.card V := Nat.lt_of_not_ge h
    obtain ⟨Y, hXY, hYdraw⟩ :=
      WilliamsonShmoys.drawable_graph_edge_augmentation X hdraw hV hsmall
    have heq : Y = X := hmax Y (le_of_lt hXY) hYdraw
    exact (lt_irrefl X (heq ▸ hXY))
  omega