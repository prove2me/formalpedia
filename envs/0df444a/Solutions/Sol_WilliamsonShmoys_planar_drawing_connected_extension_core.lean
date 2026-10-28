-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:37:07.494163+00:00
-- url     : https://prove2.me/submissions/b8b60260-1e4f-4e7f-80ed-e6a87f999a2d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_step_of_three_vertices
import Theorems.Thm_WilliamsonShmoys_finite_connected_extension_of_edge_step

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ S : SimpleGraph V,
      T ≤ S ∧ HasPlanarDrawingOn S ∧ S.Connected := by
  apply WilliamsonShmoys.finite_connected_extension_of_edge_step
    (T := T) (P := HasPlanarDrawingOn) hT
  intro G hTG hPG hDisconnected
  exact WilliamsonShmoys.planar_drawing_connected_step_of_three_vertices
    G hPG hCard hDisconnected
