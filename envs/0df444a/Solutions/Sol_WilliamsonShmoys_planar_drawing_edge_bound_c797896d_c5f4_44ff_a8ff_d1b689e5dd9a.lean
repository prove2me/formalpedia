-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_c797896d_c5f4_44ff_a8ff_d1b689e5dd9a
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:21:59.986588+00:00
-- url     : https://prove2.me/submissions/3fc6af40-dc9c-4958-aae7-3b7e377ade5e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_triangulation_extension_c797896d_c5f4_44ff_a8ff_d1b689e5dd9a

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨G, hsub, _hDrawG, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_edge_bound_triangulation_extension_c797896d_c5f4_44ff_a8ff_d1b689e5dd9a
      M hV hDraw
  calc
    M.edgeSet.ncard ≤ G.edgeSet.ncard := Set.ncard_mono hsub
    _ = 3 * Fintype.card V - 6 := hcard