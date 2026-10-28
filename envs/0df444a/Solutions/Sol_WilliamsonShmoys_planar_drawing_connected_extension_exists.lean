-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:43:26.164553+00:00
-- url     : https://prove2.me/submissions/fe58dd1b-91e6-443b-b0af-1b0ecaa0f175
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_connected_component_fintype
import Theorems.Thm_WilliamsonShmoys_connected_supergraph_of_component_step
import Theorems.Thm_WilliamsonShmoys_planar_drawing_component_merge

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ Z : SimpleGraph V,
      Y ≤ Z ∧ Z.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn Z := by
  exact WilliamsonShmoys.connected_supergraph_of_component_step
    (P := WilliamsonShmoys.HasPlanarDrawingOn)
    WilliamsonShmoys.connected_component_fintype
    (fun G hG hDisconnected iG =>
      WilliamsonShmoys.planar_drawing_component_merge G hV hG hDisconnected iG)
    Y hY