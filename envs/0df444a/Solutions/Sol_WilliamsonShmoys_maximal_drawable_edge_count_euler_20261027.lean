-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_euler_20261027
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:22:41.867389+00:00
-- url     : https://prove2.me/submissions/0108ce98-3592-48e4-8f20-ee240a625c88
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_extension_euler

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hmax : forall R : SimpleGraph V,
      (forall {u v}, Q.Adj u v -> R.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn R -> R = Q)
    (hV : 3 <= Fintype.card V) :
    Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨R, hsub, hRdraw, hRcount⟩ :=
    WilliamsonShmoys.planar_drawable_maximal_extension_euler Q hdraw hV
  have hRQ : R = Q := hmax R hsub hRdraw
  rw [← hRQ]
  exact hRcount