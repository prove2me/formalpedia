-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_bound_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:41:39.506287+00:00
-- url     : https://prove2.me/submissions/58bdc683-0673-43e9-929c-6cb685680ceb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_augmentation

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (U : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ W : SimpleGraph V, U ≤ W →
      WilliamsonShmoys.HasPlanarDrawingOn W → W = U)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ U.edgeSet.ncard + 6 := by
  obtain ⟨W, hUW, hWdraw, hcount⟩ :=
    WilliamsonShmoys.planar_graph_triangulation_augmentation U hdraw hV
  have hWU : W = U := hmax W hUW hWdraw
  rw [hWU] at hcount
  exact le_of_eq hcount