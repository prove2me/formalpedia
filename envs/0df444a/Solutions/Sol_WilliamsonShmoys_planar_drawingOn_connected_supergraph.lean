-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_connected_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:01:37.761781+00:00
-- url     : https://prove2.me/submissions/df26927e-f797-40aa-b9f5-e38e4b694d37
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_component_step
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_finite_merge_iteration

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hV : 3 <= Fintype.card V) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧ Q.Connected := by
  apply WilliamsonShmoys.planar_drawingOn_finite_merge_iteration P hdraw
  intro R hPR hR hnotConnected
  exact WilliamsonShmoys.planar_drawingOn_component_step R hR hV hnotConnected