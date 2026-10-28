-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_bound_for_augmentation_2fefb580
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:53:44.520321+00:00
-- url     : https://prove2.me/submissions/8f00fdbb-dcf4-4092-ac60-f20c103ca237
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulated_augmentation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hUdraw : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hUmax : ∀ W : SimpleGraph V,
      U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W = U)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ U.edgeSet.ncard + 6 := by
  obtain ⟨W, hUW, hWdraw, hEdges⟩ :=
    WilliamsonShmoys.drawable_graph_has_triangulated_augmentation U hUdraw hCard
  have hEq : W = U := hUmax W hUW hWdraw
  rw [hEq] at hEdges
  exact hEdges.le